/-
# Cassels, Chapter 11, Lemma 7.1: exceptional numbers of ternary genera

**Layer:** lattices `L : Lat ℚ n` on a regular space $(\mathbb Q^n, Q)$, $n \ge 3$ (Cassels: $n = 3$); localizations
`loc v L` at the finite primes, given at the odd prime $p$ of the place `v` by a basis `γ` (`loc v L = locAct v γ (std v)`)
with Gram matrix `locGram Q v γ`; primitive vectors `LatPrimitive`, `LocPrimitive` (`Ch11Sec7.lean`); the proper spinor
genus `SameProperSpinorGenus` (Cassels' spinor genus).

**Defines** (Cassels, Ch. 11, p. 229): `SpnRepresentsPrim Q M a` — $a$ is represented primitively by the spinor genus of
$M$ (by some lattice of it); `IsExceptional Q L a` — $a$ is *exceptional* for the genus of $L$: represented primitively
by at least one but not by all of the spinor genera in the genus.

**Proves** Cassels' Lemma 7.1 (p. 229) (`isExceptional_iff_mul_sq`): *let $p \ne 2$ be a prime not dividing the
determinant of a genus of integral ternary forms; then for an integer $a \ne 0$, $a$ is exceptional if and only if
$ap^2$ is.* Lattice form: "$p \nmid d$, integral" is the hypothesis at $p$ only — $L_p$ is integral (`hint`) and
unimodular (`hdet`); nothing is assumed at the other primes, and any $n \ge 3$ is allowed.

*Proof.* The argument is Cassels': a substitution of type (ii) at $p$ (Theorem 3.1) moves the spinor genera of the
genus by a fixed element $g(p)$ of $G$ and turns a primitive representation of $a$ into one of $ap^2$, and back. Here
the substitution is a rotation $R(t)$ of a hyperbolic plane of $L_p$ ($e \mapsto te$, $f \mapsto t^{-1}f$,
`hrot`), with $t = p^{\mp1}$: for a primitive $x \in N_p$ there is an isotropic $e \in N_p$ with $B(x, e) = 1$
(`exists_isotropic_qbil_eq_one`; Cassels (7.5)–(7.6), reconstructed — the formulas are lost in the scan), and with
$f = x - Q(x)e$ the vector $sx$ ($s = p^{\pm1}$) is primitive in $R(s^{-1})N_p$ (`exists_locPrimitive_smul`). Since
$\theta(R(s^{-1})) = s$ and $\theta(O^+(N_p))$ contains the units, all these lattices lie in the spinor genus of
$\beta N$ for one fixed adele $\beta$ with $\theta(\beta_p) = p$ (`sameProperSpinorGenus_of_unit_class`, by Lemma 1.4 (iv)).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec7
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local
import QuadFormsKB.Literature.Cassels.Ch11Sec1Criterion
import QuadFormsKB.Literature.Cassels.Ch11Sec3GroupY
import QuadFormsKB.Lattices.SAEqualPairs
import QuadFormsKB.Literature.Cassels.Ch11Sec3Thm

open NumberField IsDedekindDomain Matrix Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### Local constructions at an odd unimodular prime -/

section Local

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {Q : QuadForm F n} {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem smul_mem_of_valued_le_one' {M : Submodule 𝔬 (Fin n → Fv)} {y : Fin n → Fv} (hy : y ∈ M) {c : Fv}
    (hc : Valued.v c ≤ 1) : c • y ∈ M :=
  M.smul_mem (⟨c, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩ : 𝔬) hy

/-- **A primitive vector has a unit coordinate** in any basis of the lattice. -/
theorem exists_unit_coord {γ : GL (Fin n) Fv} {x : Fin n → Fv}
    (hx : LocPrimitive v (locAct v γ (std v)) x) :
    ∃ ξ ∈ std v, γ.val *ᵥ ξ = x ∧ ∃ i, Valued.v (ξ i) = 1 := by
  obtain ⟨ξ, hξ, rfl⟩ := mem_locAct.mp hx.1
  refine ⟨ξ, hξ, rfl, ?_⟩
  by_contra h
  push Not at h
  have hlt : ∀ i, Valued.v (ξ i) < 1 := fun i => lt_of_le_of_ne (mem_std_iff.mp hξ i) (h i)
  set P : Fv := ((LocalDensity.NF.π v : 𝔬) : Fv)
  have hP : Valued.v P = WithZero.exp (-1 : ℤ) := LocalDensity.NF.valued_π v
  have hmem : P⁻¹ • (γ.val *ᵥ ξ) ∈ locAct v γ (std v) := by
    refine mem_locAct.mpr ⟨P⁻¹ • ξ, mem_std_iff.mpr fun i => ?_, by rw [Matrix.mulVec_smul]⟩
    rw [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, hP]
    have h1 : Valued.v (ξ i) ≤ WithZero.exp (-1 : ℤ) := HN.valued_le_exp_neg_one v (hlt i)
    calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v (ξ i) ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) :=
          mul_le_mul' le_rfl h1
      _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
  have := hx.2 _ hmem
  rw [map_inv₀, hP, ← WithZero.exp_neg, neg_neg] at this
  exact absurd this (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)

/-- Three distinct indices. -/
theorem exists_three_ne (hn : 3 ≤ n) (i : Fin n) : ∃ j k : Fin n, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := ⟨if (i : ℕ) = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
    split_ifs with h <;> intro he <;> simp [Fin.ext_iff] at he <;> omega⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset (Fin n)) ⊆ {i, j} := fun k _ => by
      by_cases hki : k = i
      · simp [hki]
      · simp [h k hki]
    have := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin] at this
    have := this.trans Finset.card_le_two
    omega
  exact ⟨j, k, hj, hk1, fun h => hk2 h.symm⟩

/-- **An isotropic vector pairing to $1$ with a primitive vector** (the normal form behind Cassels (7.5)–(7.6), p. 229):
if $L_\mathfrak p$ is integral and unimodular, $\mathfrak p \nmid 2$, $n \ge 3$, and $x$ is primitive in $L_\mathfrak p$,
then there is $e \in L_\mathfrak p$ with $Q(e) = 0$ and $B(x, e) = 1$. *Proof:* in an orthogonal basis $b_k$
($B(b_k, b_k) = g_k$ units), let $\xi_i$ be a unit coordinate of $x$ and $g_js^2 + g_kt^2 = -g_i$; one of
$b_i \pm (sb_j + tb_k)$ pairs with $x$ to a unit (the two pairings add up to $2g_i\xi_i$). -/
theorem exists_isotropic_qbil_eq_one (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hn : 3 ≤ n)
    (L : Lat F n) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1) (hdet : Valued.v (locGram Q v γ).det = 1)
    {x : Fin n → Fv} (hx : LocPrimitive v (loc v L.1) x) :
    ∃ e ∈ loc v L.1, Q.evalIn Fv e = 0 ∧ qbil Q Fv x e = 1 := by
  classical
  obtain ⟨γ', ν, hγ', horth, hval, hdet'⟩ := exists_diag_basis hQ h2 L γ hγ hint
  set G := locGram Q v γ' with hG
  -- the diagonal entries are units
  have hunit : ∀ k, Valued.v (G k k) = 1 := by
    have hGd : G = Matrix.diagonal fun k => G k k := by
      refine Matrix.ext fun k l => ?_
      by_cases h : k = l
      · subst h; simp
      · rw [Matrix.diagonal_apply_ne _ h]; exact horth k l h
    have hprod : Valued.v G.det = ∏ k, Valued.v (G k k) := by
      conv_lhs => rw [hGd]
      rw [Matrix.det_diagonal, map_prod]
    have hle : ∀ k, Valued.v (G k k) ≤ 1 := fun k => by
      rw [hval k, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    intro k
    by_contra hk
    have hlt : Valued.v (G k k) < 1 := lt_of_le_of_ne (hle k) hk
    have : ∏ l, Valued.v (G l l) < 1 := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
      calc Valued.v (G k k) * ∏ l ∈ Finset.univ.erase k, Valued.v (G l l)
          ≤ Valued.v (G k k) * 1 := mul_le_mul' le_rfl (Finset.prod_le_one fun l _ => hle l)
        _ < 1 := by rw [mul_one]; exact hlt
    rw [← hprod, hG, hdet', hdet] at this
    exact lt_irrefl _ this
  have hG0 : ∀ k, G k k ≠ 0 := fun k h0 => by
    have := hunit k; rw [h0, map_zero] at this; exact zero_ne_one this
  rw [hγ'] at hx
  obtain ⟨ξ, hξ, rfl, i, hi⟩ := exists_unit_coord hx
  obtain ⟨j, k, hji, hki, hjk⟩ := exists_three_ne hn i
  -- `g_j s² + g_k t² = -g_i`
  have hu : ∀ l, Valued.v (-(G l l) / G i i) = 1 := fun l => by
    rw [map_div₀, Valuation.map_neg, hunit, hunit, div_one]
  have hU : ∀ l, IsUnit (toO v (-(G l l) / G i i) (hu l).le) := fun l =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr (hu l)
  obtain ⟨s, t, hst⟩ := Nbr.exists_binary_one_dvr (LocalDensity.NF.irreducible_π v)
    (LocalDensity.NF.π_not_dvd_two v h2) (hU j) (hU k)
  have hst' : G i i + G j j * (s : Fv) ^ 2 + G k k * (t : Fv) ^ 2 = 0 := by
    have := congrArg (fun z : 𝔬 => (z : Fv)) hst
    push_cast at this
    change -(G j j) / G i i * (s : Fv) ^ 2 + -(G k k) / G i i * (t : Fv) ^ 2 = 1 at this
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq (hG0 i)] at this
    linear_combination -this
  have hs1 : Valued.v (s : Fv) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp s.2
  have ht1 : Valued.v (t : Fv) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp t.2
  -- the two candidates `c₊, c₋`
  let c : Fv → Fin n → Fv := fun ε => Pi.single i 1 + Pi.single j (ε * s) + Pi.single k (ε * t)
  have hci : ∀ ε, c ε i = 1 := fun ε => by simp [c, hji.symm, hki.symm]
  have hcj : ∀ ε, c ε j = ε * s := fun ε => by simp [c, hji, hjk]
  have hck : ∀ ε, c ε k = ε * t := fun ε => by simp [c, hki, hjk.symm]
  have hbil : ∀ (ε : Fv) (d : Fin n → Fv), qbil Q Fv (γ'.val *ᵥ d) (γ'.val *ᵥ c ε) =
      d i * G i i + ε * (d j * (G j j * s) + d k * (G k k * t)) := by
    intro ε d
    have hGc : (fun l => G l l * c ε l) =
        Pi.single i (G i i) + Pi.single j (G j j * (ε * s)) + Pi.single k (G k k * (ε * t)) := by
      funext l
      simp only [c, Pi.add_apply, Pi.single_apply]
      by_cases hli : l = i
      · simp [hli, hji.symm, hki.symm]
      · by_cases hlj : l = j
        · simp [hlj, hji, hjk]
        · by_cases hlk : l = k
          · simp [hlk, hki, hjk.symm]
          · simp [hli, hlj, hlk]
    have hmv : G *ᵥ c ε = fun l => G l l * c ε l := funext (locGram_mulVec_diag horth (c ε))
    rw [qbil_mulVec_locGram, hmv, hGc, dotProduct_add, dotProduct_add, dotProduct_single, dotProduct_single,
      dotProduct_single]
    ring
  have hiso : ∀ ε : Fv, ε ^ 2 = 1 → Q.evalIn Fv (γ'.val *ᵥ c ε) = 0 := by
    intro ε hε
    have h2v : (2 : Fv) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2v
    rw [two_mul_evalIn_eq, hbil, hci, hcj, hck, mul_zero]
    linear_combination (1 : Fv) * hst' + (G j j * s ^ 2 + G k k * t ^ 2) * hε
  have hmemc : ∀ ε : Fv, Valued.v ε ≤ 1 → γ'.val *ᵥ c ε ∈ locAct v γ' (std v) := by
    intro ε hε
    refine mem_locAct.mpr ⟨c ε, ?_, rfl⟩
    refine (std v).add_mem ((std v).add_mem (single_mem_std i (by simp)) (single_mem_std j ?_))
      (single_mem_std k ?_)
    · rw [map_mul]; exact mul_le_one' hε hs1
    · rw [map_mul]; exact mul_le_one' hε ht1
  -- one of the two pairings is a unit
  set A := ξ i * G i i
  set Bt := ξ j * (G j j * s) + ξ k * (G k k * t)
  have hA : Valued.v A = 1 := by rw [map_mul, hi, hunit, one_mul]
  have hpair : ∀ ε, qbil Q Fv (γ'.val *ᵥ ξ) (γ'.val *ᵥ c ε) = A + ε * Bt := fun ε => hbil ε ξ
  obtain ⟨ε, hε2, hεv, hεu⟩ : ∃ ε : Fv, ε ^ 2 = 1 ∧ Valued.v ε ≤ 1 ∧ Valued.v (A + ε * Bt) = 1 := by
    by_cases h1 : Valued.v (A + 1 * Bt) = 1
    · exact ⟨1, by ring, by simp, h1⟩
    · refine ⟨-1, by ring, by simp, ?_⟩
      have hle : ∀ ε : Fv, Valued.v ε ≤ 1 → Valued.v (A + ε * Bt) ≤ 1 := by
        intro ε hε
        have hξ' := mem_std_iff.mp hξ
        refine Valuation.map_add_le _ (hA.le) ?_
        rw [map_mul]
        refine mul_le_one' hε (Valuation.map_add_le _ ?_ ?_) <;> rw [map_mul, map_mul] <;>
          refine mul_le_one' (hξ' _) (mul_le_one' (by rw [hunit]) ?_)
        · exact hs1
        · exact ht1
      by_contra h2'
      have hlt1 : Valued.v (A + 1 * Bt) < 1 := lt_of_le_of_ne (hle 1 (by simp)) h1
      have hlt2 : Valued.v (A + -1 * Bt) < 1 := lt_of_le_of_ne (hle (-1) (by simp)) h2'
      have hsum : Valued.v ((A + 1 * Bt) + (A + -1 * Bt)) < 1 := Valuation.map_add_lt _ hlt1 hlt2
      have h2A : (A + 1 * Bt) + (A + -1 * Bt) = 2 * A := by ring
      rw [h2A, map_mul, valued_two h2, hA, one_mul] at hsum
      exact lt_irrefl _ hsum
  set w := A + ε * Bt
  have hw0 : w ≠ 0 := fun h0 => by rw [h0, map_zero] at hεu; exact zero_ne_one hεu
  refine ⟨w⁻¹ • (γ'.val *ᵥ c ε), ?_, ?_, ?_⟩
  · rw [hγ']
    exact smul_mem_of_valued_le_one' (hmemc ε hεv) (by rw [map_inv₀, hεu, inv_one])
  · rw [QuadForm.evalIn_smul, hiso ε hε2, mul_zero]
  · rw [qbil_comm, qbil_smul_left, qbil_comm, hpair, inv_mul_cancel₀ hw0]

/-- **The substitution of type (ii) at $\mathfrak p$, locally** (Cassels (7.7)–(7.12), p. 229, reconstructed): if
$L_\mathfrak p$ is integral and unimodular ($\mathfrak p \nmid 2$, $n \ge 3$), $x$ is primitive in $L_\mathfrak p$ and
$s \ne 0$ with $s^2Q(x)$ integral, there is a rotation $g$ of $V_\mathfrak p$ with $\theta(g) = sF_\mathfrak p^{\times 2}$
such that $sx$ is primitive in $gL_\mathfrak p$. Namely $g = R(s^{-1})$ on the hyperbolic plane $\langle e, f\rangle$,
$f = x - Q(x)e$ (`exists_isotropic_qbil_eq_one`), and $sx = g(f + s^2Q(x)e)$. -/
theorem exists_locPrimitive_smul (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hn : 3 ≤ n)
    (L : Lat F n) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1) (hdet : Valued.v (locGram Q v γ).det = 1)
    {x : Fin n → Fv} (hx : LocPrimitive v (loc v L.1) x) {s : Fv} (hs : s ≠ 0)
    (hsx : Valued.v (s ^ 2 * Q.evalIn Fv x) ≤ 1) :
    ∃ g ∈ Tamagawa.soSub Q Fv, spinorNorm Q Fv g = sqClassOf s ∧
      LocPrimitive v (locAct v ((g : orthGroup Q Fv) : GL (Fin n) Fv) (loc v L.1)) (s • x) := by
  obtain ⟨e, he, heQ, hxe⟩ := exists_isotropic_qbil_eq_one hQ h2 hn L γ hγ hint hdet hx
  set a := Q.evalIn Fv x with ha
  set f := x - a • e with hfdef
  have hee : qbil Q Fv e e = 0 := by rw [qbil_self, heQ, mul_zero]
  have hex : qbil Q Fv e x = 1 := by rw [qbil_comm, hxe]
  have hfQ : Q.evalIn Fv f = 0 := by
    apply mul_left_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0)
    rw [two_mul_evalIn_eq, mul_zero, hfdef, qbil_sub_left, qbil_sub_right, qbil_sub_right, qbil_smul_left,
      qbil_smul_left, qbil_smul_right, qbil_smul_right, qbil_self, hxe, hex, hee, ← ha]
    ring
  have hef : qbil Q Fv e f = 1 := by
    rw [hfdef, qbil_sub_right, qbil_smul_right, hex, hee, mul_zero, sub_zero]
  have hfe : qbil Q Fv f e = 1 := by rw [qbil_comm, hef]
  have hff : qbil Q Fv f f = 0 := by rw [qbil_self, hfQ, mul_zero]
  have hs' : s⁻¹ ≠ 0 := inv_ne_zero hs
  -- the rotation
  have hQ1 : Q.evalIn Fv (e + (1 : Fv) • f) = 1 := evalIn_hvec heQ hfQ hef 1
  have hQs : Q.evalIn Fv (e + s⁻¹ • f) = s⁻¹ := evalIn_hvec heQ hfQ hef s⁻¹
  obtain ⟨hso, hθ⟩ := symm_mul_symm_spec hQ (x := e + (1 : Fv) • f) (y := e + s⁻¹ • f)
    (by rw [hQs]; exact hs') hs (by rw [hQ1, hQs, mul_inv_cancel₀ hs])
  refine ⟨_, hso, hθ, ?_⟩
  -- the preimage `y₀ = f + s²Q(x)e`
  have haint : Valued.v a ≤ 1 := hint x hx.1
  have hfmem : f ∈ loc v L.1 := (loc v L.1).sub_mem hx.1 (smul_mem_of_valued_le_one' he haint)
  set y₀ := f + (s ^ 2 * a) • e with hy₀
  have hy₀mem : y₀ ∈ loc v L.1 := (loc v L.1).add_mem hfmem (smul_mem_of_valued_le_one' he hsx)
  have hy₀e : qbil Q Fv y₀ e = 1 := by
    rw [hy₀, qbil_add_left, qbil_smul_left, hfe, hee, mul_zero, add_zero]
  have hy₀prim : LocPrimitive v (loc v L.1) y₀ := by
    refine ⟨hy₀mem, fun t ht => ?_⟩
    have := qbil_le_one_of_int hint ht he
    rwa [qbil_smul_left, hy₀e, mul_one] at this
  have himg : (((symm Q Fv (e + (1 : Fv) • f) * symm Q Fv (e + s⁻¹ • f) : orthGroup Q Fv) : GL (Fin n) Fv) :
      Matrix (Fin n) (Fin n) Fv) *ᵥ y₀ = s • x := by
    rw [symm_hvec_mul_symm_hvec_mulVec heQ hfQ hef one_ne_zero hs']
    have h1 : qbil Q Fv f y₀ = s ^ 2 * a := by
      rw [hy₀, qbil_add_right, qbil_smul_right, hff, hfe, zero_add, mul_one]
    have h2' : qbil Q Fv e y₀ = 1 := by
      rw [hy₀, qbil_add_right, qbil_smul_right, hef, hee, mul_zero, add_zero]
    rw [h1, h2', hy₀, hfdef]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have := hy₀prim.locAct (((symm Q Fv (e + (1 : Fv) • f) * symm Q Fv (e + s⁻¹ • f) : orthGroup Q Fv)) :
    GL (Fin n) Fv)
  rwa [himg] at this

end Local

/-! ### Exceptional numbers -/

section Defs

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **$a$ is represented primitively by the spinor genus of $M$** (Cassels, Ch. 11, p. 229): some lattice of the
(proper) spinor genus of $M$ has a primitive vector $x$ with $Q(x) = a$. -/
@[kb "cassels1978" "Ch. 11, p. 229 (represented primitively by a spinor genus)"]
def SpnRepresentsPrim (M : Lat F n) (a : F) : Prop :=
  ∃ N : Lat F n, SameProperSpinorGenus Q M N ∧ ∃ x, LatPrimitive N.1 x ∧ Q.evalIn F x = a

/-- **$a$ is exceptional for the genus of $L$** (Cassels, Ch. 11, p. 229): $a$ is represented primitively by at least
one but not by all of the spinor genera in the genus. -/
@[kb "cassels1978" "Ch. 11, p. 229 (exceptional number of a genus)"]
def IsExceptional (L : Lat F n) (a : F) : Prop :=
  (∃ M : Lat F n, SameGenus Q L.1 M.1 ∧ SpnRepresentsPrim Q M a) ∧
    ∃ M : Lat F n, SameGenus Q L.1 M.1 ∧ ¬ SpnRepresentsPrim Q M a

end Defs

section Global

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ} {Q : QuadForm ℚ n}

/-- **A primitive vector of $L$ is primitive in every $L_p$.** -/
theorem locPrimitive_of_latPrimitive {L : Lat ℚ n} {x : Fin n → ℚ} (hx : LatPrimitive L.1 x)
    (v : HeightOneSpectrum (𝓞 ℚ)) : LocPrimitive v (loc v L.1) (locVec v x) := by
  refine ⟨locVec_mem_loc v hx.1, fun t ht => ?_⟩
  by_contra hlt
  push Not at hlt
  have ht0 : t ≠ 0 := fun h0 => by rw [h0, map_zero] at hlt; exact not_lt_of_ge zero_le hlt
  set p : ℚ := ((natGenUnit v : ℚˣ) : ℚ) with hp
  have hp0 : p ≠ 0 := Units.ne_zero _
  have hpv : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) p) = WithZero.exp (-1 : ℤ) := valued_natGenUnit_self v
  have hlocsmul : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ),
      locVec w (c • x) = algebraMap ℚ (w.adicCompletion ℚ) c • locVec w x := fun w c => by
    rw [LinearMap.map_smul]; funext i; simp [Algebra.smul_def]
  have hmem : p⁻¹ • x ∈ L.1 := by
    rw [mem_iff_forall_loc L.2]
    intro w
    rw [hlocsmul]
    by_cases hw : w = v
    · subst hw
      have e : algebraMap ℚ (w.adicCompletion ℚ) p⁻¹ • locVec w x =
          (algebraMap ℚ (w.adicCompletion ℚ) p⁻¹ * t⁻¹) • (t • locVec w x) := by
        rw [smul_smul, mul_assoc, inv_mul_cancel₀ ht0, mul_one]
      rw [e]
      refine smul_mem_of_valued_le_one' ht ?_
      have h1 : WithZero.exp (1 : ℤ) ≤ Valued.v t := by
        have := HN.valued_le_exp_neg_one w (x := t⁻¹) (by
          rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt)
        rw [map_inv₀, inv_le_comm₀ (lt_trans zero_lt_one hlt) (zero_lt_iff.mpr WithZero.exp_ne_zero)] at this
        rwa [← WithZero.exp_neg, neg_neg] at this
      rw [map_mul, map_inv₀, map_inv₀, map_inv₀, hpv, ← WithZero.exp_neg, neg_neg]
      calc WithZero.exp (1 : ℤ) * (Valued.v t)⁻¹ ≤ Valued.v t * (Valued.v t)⁻¹ := mul_le_mul' h1 le_rfl
        _ = 1 := mul_inv_cancel₀ (by rw [Valuation.ne_zero_iff]; exact ht0)
    · refine smul_mem_of_valued_le_one' (locVec_mem_loc w hx.1) ?_
      rw [map_inv₀, map_inv₀, valued_natGenUnit_of_ne hw, inv_one]
  obtain ⟨r, hr⟩ := hx.2 _ hmem
  have hle : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) p⁻¹) ≤ 1 := by
    rw [← hr, valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one v r
  rw [map_inv₀, map_inv₀, hpv, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  omega

/-- A unit multiple of a primitive vector is primitive. -/
theorem LocPrimitive.smul_unit {v : HeightOneSpectrum (𝓞 ℚ)} {M : Submodule (v.adicCompletionIntegers ℚ)
    (Fin n → v.adicCompletion ℚ)} {y : Fin n → v.adicCompletion ℚ} (h : LocPrimitive v M y)
    {c : v.adicCompletion ℚ} (hc : Valued.v c = 1) : LocPrimitive v M (c • y) := by
  have hc0 : c ≠ 0 := fun h0 => by rw [h0, map_zero] at hc; exact zero_ne_one hc
  refine ⟨smul_mem_of_valued_le_one' h.1 hc.le, fun t ht => ?_⟩
  rw [smul_smul] at ht
  have := h.2 _ ht
  rwa [map_mul, hc, mul_one] at this

/-- **Integral unimodular localizations are a genus invariant.** -/
theorem exists_loc_basis_of_sameGenus {v : HeightOneSpectrum (𝓞 ℚ)} {L M : Lat ℚ n}
    (hM : SameGenus Q L.1 M.1) {γ : GL (Fin n) (v.adicCompletion ℚ)} (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1)
    (hdet : Valued.v (locGram Q v γ).det = 1) :
    ∃ γ' : GL (Fin n) (v.adicCompletion ℚ), loc v M.1 = locAct v γ' (std v) ∧
      (∀ x ∈ loc v M.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧ Valued.v (locGram Q v γ').det = 1 := by
  obtain ⟨g, hg, hgM⟩ := hM v
  refine ⟨g * γ, by rw [locAct_mul, ← hγ, hgM], fun x hx => ?_, ?_⟩
  · rw [← hgM] at hx
    obtain ⟨y, hy, rfl⟩ := mem_locAct.mp hx
    rw [evalIn_mulVec_of_mem Q hg]
    exact hint y hy
  · have : locGram Q v (g * γ) = locGram Q v γ := by
      refine Matrix.ext fun k l => ?_
      rw [← locGram_apply_eq, ← locGram_apply_eq, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
      exact qbil_orth Q _ ⟨g, hg⟩ _ _
    rw [this, hdet]

/-- **An adele at one prime:** an element of $O(V_\mathfrak p)$ at $\mathfrak p$ and $1$ elsewhere. -/
theorem exists_oaf_single (v : HeightOneSpectrum (𝓞 ℚ)) (g : orthGroup Q (v.adicCompletion ℚ)) :
    ∃ α : OAf Q, α v = g ∧ ∀ w, w ≠ v → α w = 1 := by
  classical
  refine ⟨⟨fun w => if h : w = v then h ▸ g else 1, ?_⟩, by simp, fun w hw => by simp [hw]⟩
  filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
  have hw' : w ≠ v := hw
  simp only [hw', ↓reduceDIte]
  exact (stdStab Q w).one_mem

/-- **Shifting spinor genera by a unit spinor norm class** (Cassels' $g(p)$, by Lemma 1.4 (iv)): if $\alpha, \beta$ are
adeles which are $1$ away from $\mathfrak p$ and rotations at $\mathfrak p$, $L_\mathfrak p$ is integral and unimodular
($\mathfrak p \nmid 2$), and $\theta(\alpha_\mathfrak p)\theta(\beta_\mathfrak p)$ is a unit class, then $\alpha L$ and
$\beta L$ lie in the same spinor genus. -/
theorem sameProperSpinorGenus_of_unit_class (hQ : Q.Nondegenerate) (hn : 2 ≤ n) {v : HeightOneSpectrum (𝓞 ℚ)}
    (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) (M : Lat ℚ n) {γ : GL (Fin n) (v.adicCompletion ℚ)}
    (hγ : loc v M.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v M.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1)
    (hdet : Valued.v (locGram Q v γ).det = 1) (α β : OAf Q) (hα1 : ∀ w, w ≠ v → α w = 1)
    (hβ1 : ∀ w, w ≠ v → β w = 1) (hαv : α v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ))
    (hβv : β v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ))
    (hθ : IsUnitSqClass v (spinorNorm Q (v.adicCompletion ℚ) (α v) * spinorNorm Q (v.adicCompletion ℚ) (β v))) :
    SameProperSpinorGenus Q (latSMul Q β M) (latSMul Q α M) := by
  have hrot : ∀ (δ : OAf Q), (∀ w, w ≠ v → δ w = 1) → δ v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ) →
      ∀ w, δ w ∈ Tamagawa.soSub Q (w.adicCompletion ℚ) := fun δ h1 hv w => by
    by_cases hw : w = v
    · subst hw; exact hv
    · rw [h1 w hw]; exact (Tamagawa.soSub Q _).one_mem
  refine (sameProperSpinorGenus_smul_iff Q hQ M β α (hrot β hβ1 hβv) (hrot α hα1 hαv)).mpr
    ⟨1, (Tamagawa.soSub Q ℚ).one_mem, fun w => ?_⟩
  have h1 : spinorNorm Q (w.adicCompletion ℚ) (orthMap Q (w.adicCompletion ℚ) 1) = 1 := by
    rw [map_one, ← spinorNormHom_apply Q _ hQ, map_one]
  by_cases hw : w = v
  · subst hw
    obtain ⟨u, hu, hc⟩ := hθ
    have hu0 : u ≠ 0 := fun h0 => by rw [h0, map_zero] at hu; exact zero_ne_one hu
    have hmem := (mem_localSpinorNormGroup_iff_of_unimodular (Q := Q) (v := w) hQ h2 hn M γ hγ hint hdet (Units.mk0 u hu0)).mpr
      ⟨u, hu, by rw [sqClassOf_of_ne_zero hu0]⟩
    obtain ⟨σ, hσ, hσθ⟩ := (mem_localSpinorNormGroup Q hQ w M).mp hmem
    refine ⟨σ, hσ, ?_⟩
    rw [h1, mul_one, hσθ, hc, sqClassOf_of_ne_zero hu0]
  · refine ⟨1, ⟨(locStabV Q w M).one_mem, (Tamagawa.soSub Q _).one_mem⟩, ?_⟩
    rw [hα1 w hw, hβ1 w hw, h1, ← spinorNormHom_apply Q _ hQ, map_one, one_mul, one_mul]

/-- **Moving a primitive representation by the substitution at $\mathfrak p$** (Cassels, proof of Lemma 7.1,
(7.7)–(7.12)): if $a$ is represented primitively by the spinor genus of $M$ (in the genus of $L$, which is integral and
unimodular at $\mathfrak p \nmid 2$), $s \in \mathbb Q^\times$ is a unit away from $\mathfrak p$ with $s^2a$ integral at
$\mathfrak p$, and $\beta$ is an adele, $1$ away from $\mathfrak p$, with $\theta(\beta_\mathfrak p) \in sU_p(\mathbb Q_p^\times)^2$,
then $s^2a$ is represented primitively by the spinor genus of $\beta M$. -/
theorem spnRepresentsPrim_shift (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {v : HeightOneSpectrum (𝓞 ℚ)}
    (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) {L : Lat ℚ n} {γ : GL (Fin n) (v.adicCompletion ℚ)}
    (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1)
    (hdet : Valued.v (locGram Q v γ).det = 1) {M : Lat ℚ n} (hM : SameGenus Q L.1 M.1) (β : OAf Q)
    (hβ1 : ∀ w, w ≠ v → β w = 1) (hβv : β v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ)) {s : ℚ} (hs : s ≠ 0)
    (hsw : ∀ w, w ≠ v → Valued.v (algebraMap ℚ (w.adicCompletion ℚ) s) = 1)
    (hθ : IsUnitSqClass v (sqClassOf (algebraMap ℚ (v.adicCompletion ℚ) s) *
      spinorNorm Q (v.adicCompletion ℚ) (β v)))
    {a : ℚ} (ha : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (s ^ 2 * a)) ≤ 1)
    (h : SpnRepresentsPrim Q M a) : SpnRepresentsPrim Q (latSMul Q β M) (s ^ 2 * a) := by
  obtain ⟨N, hMN, x, hx, hxa⟩ := h
  have hN : SameGenus Q L.1 N.1 :=
    SameGenus.trans Q hM (SameSpinorGenus.sameGenus Q (SameProperSpinorGenus.sameSpinorGenus Q hMN))
  obtain ⟨γN, hγN, hintN, hdetN⟩ := exists_loc_basis_of_sameGenus hN hγ hint hdet
  have hxv := locPrimitive_of_latPrimitive hx v
  have hsv : algebraMap ℚ (v.adicCompletion ℚ) s ≠ 0 := (map_ne_zero _).mpr hs
  obtain ⟨g, hg, hgθ, hgprim⟩ := exists_locPrimitive_smul hQ h2 hn N γN hγN hintN hdetN hxv hsv (by
    rw [evalIn_locVec]
    change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) s ^ 2 *
      algebraMap ℚ (v.adicCompletion ℚ) (Q.evalIn ℚ x)) ≤ 1
    rw [hxa, ← map_pow, ← map_mul]
    exact ha)
  obtain ⟨α, hαv, hα1⟩ := exists_oaf_single v g
  have hlocsmul : ∀ (w : HeightOneSpectrum (𝓞 ℚ)),
      locVec w (s • x) = algebraMap ℚ (w.adicCompletion ℚ) s • locVec w x := fun w => by
    rw [LinearMap.map_smul]; funext i; simp [Algebra.smul_def]
  refine ⟨latSMul Q α N, ?_, s • x, ?_, ?_⟩
  · refine SameProperSpinorGenus.trans Q (sameProperSpinorGenus_smul_left Q hQ β hMN) ?_
    exact sameProperSpinorGenus_of_unit_class hQ (by omega) h2 N hγN hintN hdetN α β hα1 hβ1
      (by rw [hαv]; exact hg) hβv (by rw [hαv, hgθ]; exact hθ)
  · apply latPrimitive_of_forall_loc (latSMul Q α N).2
    intro w
    rw [loc_latSMul, hlocsmul]
    by_cases hw : w = v
    · subst hw; rw [hαv]; exact hgprim
    · rw [hα1 w hw, OneMemClass.coe_one, locAct_one]
      exact (locPrimitive_of_latPrimitive hx w).smul_unit (hsw w hw)
  · rw [QuadFormsKB.QuadForm.evalIn_smul, hxa]

/-- **Cassels, Lemma 7.1** (Ch. 11, p. 229), lattice form: *let $p \ne 2$ be a prime which does not divide the
determinant of a genus of integral ternary forms. Then for any integer $a \ne 0$, if one of $a, ap^2$ is exceptional,
then so is the other.* Here the genus is that of a lattice $L$ on $(\mathbb Q^n, Q)$, $n \ge 3$ (Cassels: $n = 3$); the
place `v` has prime $p$ odd (`h2`), and $L_p$ is integral (`hint`) and unimodular (`hdet`: the Gram matrix of a basis
$\gamma$ of $L_p$ has unit determinant) — this is "$p \nmid d$" for an integral form; no hypothesis at other primes is
needed, and $a = 0$ is allowed. *Proof:* module docstring. -/
@[kb "cassels1978" "Ch. 11, Lemma 7.1, p. 229 (lattice form, n ≥ 3)"]
theorem isExceptional_iff_mul_sq (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) (γ : GL (Fin n) (v.adicCompletion ℚ))
    (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1)
    (hdet : Valued.v (locGram Q v γ).det = 1) (a : ℤ) :
    IsExceptional Q L (a : ℚ) ↔ IsExceptional Q L ((Rat.HeightOneSpectrum.natGenerator v : ℚ) ^ 2 * a) := by
  classical
  let _ : MulAction (OAf Q) (Lat ℚ n) := latAction Q
  set p : ℚ := ((natGenUnit v : ℚˣ) : ℚ) with hpdef
  have hp : (Rat.HeightOneSpectrum.natGenerator v : ℚ) = p := rfl
  rw [hp]
  have hp0 : p ≠ 0 := Units.ne_zero _
  have hpv0 : algebraMap ℚ (v.adicCompletion ℚ) p ≠ 0 := (map_ne_zero _).mpr hp0
  set P : (v.adicCompletion ℚ)ˣ := Units.mk0 _ hpv0 with hP
  obtain ⟨σ, hσ, hσθ⟩ := exists_soSub_spinorNorm_eq_local Q hQ hn v P
  obtain ⟨β, hβv, hβ1⟩ := exists_oaf_single v σ
  have hβso : β v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ) := by rw [hβv]; exact hσ
  have hβθ : spinorNorm Q (v.adicCompletion ℚ) (β v) = SqClass.mk P := by rw [hβv, hσθ]
  have hβi1 : ∀ w, w ≠ v → β⁻¹ w = 1 := fun w hw => by
    change (β w)⁻¹ = 1; rw [hβ1 w hw, inv_one]
  have hβiso : β⁻¹ v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ) := (Tamagawa.soSub Q _).inv_mem hβso
  have hβiθ : spinorNorm Q (v.adicCompletion ℚ) (β⁻¹ v) = SqClass.mk P := by
    change spinorNorm Q (v.adicCompletion ℚ) (β v)⁻¹ = _
    rw [← spinorNormHom_apply Q _ hQ, map_inv, spinorNormHom_apply, hβθ, SqClass.inv_eq]
  have hsq : sqClassOf (algebraMap ℚ (v.adicCompletion ℚ) p) = SqClass.mk P := sqClassOf_of_ne_zero hpv0
  have hsqi : sqClassOf (algebraMap ℚ (v.adicCompletion ℚ) p⁻¹) = SqClass.mk P := by
    rw [map_inv₀, sqClassOf_of_ne_zero (inv_ne_zero hpv0)]
    rw [show Units.mk0 _ (inv_ne_zero hpv0) = P⁻¹ from Units.ext rfl]
    have h1 : SqClass.mk P⁻¹ * SqClass.mk P = 1 := by
      rw [← SqClass.mk_mul, inv_mul_cancel, SqClass.mk_eq_one_iff]; exact ⟨1, by simp⟩
    calc SqClass.mk P⁻¹ = SqClass.mk P⁻¹ * (SqClass.mk P * SqClass.mk P) := by rw [SqClass.mul_self, mul_one]
      _ = SqClass.mk P := by rw [← mul_assoc, h1, one_mul]
  have hunit1 : IsUnitSqClass v (SqClass.mk P * SqClass.mk P) :=
    ⟨1, by simp, by rw [SqClass.mul_self, sqClassOf_one]⟩
  have hpw : ∀ w, w ≠ v → Valued.v (algebraMap ℚ (w.adicCompletion ℚ) p) = 1 := fun w hw =>
    valued_natGenUnit_of_ne hw
  have hpwi : ∀ w, w ≠ v → Valued.v (algebraMap ℚ (w.adicCompletion ℚ) p⁻¹) = 1 := fun w hw => by
    rw [map_inv₀, map_inv₀, hpw w hw, inv_one]
  have hpvv : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) p) = WithZero.exp (-1 : ℤ) :=
    valued_natGenUnit_self v
  have ha1 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (a : ℚ)) ≤ 1 := by
    rw [valued_algebraMap, show ((a : ℚ)) = algebraMap (𝓞 ℚ) ℚ (a : 𝓞 ℚ) by simp,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one v _
  have hgen : ∀ (M : Lat ℚ n) (δ : OAf Q), SameGenus Q L.1 M.1 → SameGenus Q L.1 (latSMul Q δ M).1 :=
    fun M δ hM => SameGenus.trans Q hM (sameGenus_latSMul Q δ M)
  have P2 : ∀ M : Lat ℚ n, SameGenus Q L.1 M.1 → SpnRepresentsPrim Q M (a : ℚ) →
      SpnRepresentsPrim Q (latSMul Q β M) (p ^ 2 * a) := fun M hM h =>
    spnRepresentsPrim_shift hQ hn h2 hγ hint hdet hM β hβ1 hβso hp0 hpw (by rw [hsq, hβθ]; exact hunit1)
      (by
        rw [map_mul, map_mul, map_pow, map_pow, hpvv]
        calc WithZero.exp (-1 : ℤ) ^ 2 * Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (a : ℚ))
            ≤ 1 * 1 := mul_le_mul' (by rw [← WithZero.exp_nsmul, ← WithZero.exp_zero, WithZero.exp_le_exp, nsmul_eq_mul]; norm_num)
              ha1
          _ = 1 := one_mul 1) h
  have P3 : ∀ M : Lat ℚ n, SameGenus Q L.1 M.1 → SpnRepresentsPrim Q M (p ^ 2 * a) →
      SpnRepresentsPrim Q (latSMul Q β⁻¹ M) (a : ℚ) := fun M hM h => by
    have := spnRepresentsPrim_shift hQ hn h2 hγ hint hdet hM β⁻¹ hβi1 hβiso (inv_ne_zero hp0) hpwi
      (by rw [hsqi, hβiθ]; exact hunit1) (by
        rw [show p⁻¹ ^ 2 * (p ^ 2 * a) = (a : ℚ) by field_simp]
        exact ha1) h
    rwa [show p⁻¹ ^ 2 * (p ^ 2 * a) = (a : ℚ) by field_simp] at this
  constructor
  · rintro ⟨⟨M₁, hM₁, h₁⟩, ⟨M₂, hM₂, h₂⟩⟩
    refine ⟨⟨latSMul Q β M₁, hgen M₁ β hM₁, P2 M₁ hM₁ h₁⟩, ⟨latSMul Q β M₂, hgen M₂ β hM₂, fun h => h₂ ?_⟩⟩
    have := P3 _ (hgen M₂ β hM₂) h
    change SpnRepresentsPrim Q (β⁻¹ • β • M₂) _ at this
    rwa [inv_smul_smul] at this
  · rintro ⟨⟨M₁, hM₁, h₁⟩, ⟨M₂, hM₂, h₂⟩⟩
    refine ⟨⟨latSMul Q β⁻¹ M₁, hgen M₁ β⁻¹ hM₁, P3 M₁ hM₁ h₁⟩,
      ⟨latSMul Q β⁻¹ M₂, hgen M₂ β⁻¹ hM₂, fun h => h₂ ?_⟩⟩
    have := P2 _ (hgen M₂ β⁻¹ hM₂) h
    change SpnRepresentsPrim Q (β • β⁻¹ • M₂) _ at this
    rwa [smul_inv_smul] at this

end Global

end QuadFormsKB.Lattices
