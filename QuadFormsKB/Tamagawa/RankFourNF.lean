/-
# Reducing $\tau(SO_4) = 2$ for class number $h_F > 1$

**Layer:** a totally real number field $F$, **any class number**; `tauSO`; the rank-4 input `QuaternaryTamagawaTwo F`
(it implies $\tau = 2$, the mass formula and Siegel's formula in every rank $\ge 4$,
`tamagawaNumberTwo_of_quaternary_nf`).

Earlier files reduced the rank-4 input to the ternary one, and the ternary one to the pure quaternion forms, but only
for $\mathcal O_F$ a PID: both reductions used the change of lattice `tauSO_smul_compMat` (global Smith normal form).
With its non-PID version (`LatChange.tauSO_smul_compMat_nf`, `Tamagawa/LatticeChangeNF.lean`) they go through for
every totally real $F$:

* **`quaternaryTamagawaTwo_of_unitSplit_nf`**: `QuaternaryTamagawaTwo F` follows from $\tau = 2$ for the forms $\langle 1\rangle\perp Q_3$
  ($Q_3$ ternary); `quaternaryTamagawaTwo_of_diag_nf`: from $\tau = 2$ for the diagonal forms $\langle 1, b, c, d\rangle$, $b, c, d \in \mathcal O_F$
  (every quaternary space is similar to one of these, and $\tau$ is a similarity invariant, `LatChange.tauSO_eq_of_similar_nf`).
* **`RankFourUnitSiegel F`** (named input): Siegel's formula in rank 4 for the number $1$ and the lattices $\mathcal O_F\perp L_3$. It is a
  theorem for $\mathcal O_F$ a PID of degree $\ge 2$ (via Hilbert modular forms, `rankFourUnitSiegel_of_pid`) and for $F = \mathbb Q$ (`rankFourUnitSiegel_rat`); for $h_F > 1$ Hilbert modular forms cover only rank $\ge 6$ (`siegelFormulaAt'`, given `PrincipalPrimeSupply`).
* **`quaternaryTamagawaTwo_of_ternary_nf`**, `ternaryTamagawaTwo_of_quaternary_nf`, **`ternaryTamagawaTwo_iff_quaternary_nf`**:
  given `RankFourUnitSiegel F`, the ternary and quaternary inputs are equivalent over every totally real $F$.
* **`ternaryTamagawaTwo_of_pureForm_nf`**: `TernaryTamagawaTwo F` follows from $\tau = 2$ for the pure quaternion forms
  $\langle -a, -b, ab\rangle$ (the reduction without the PID).
* Headlines: **`tamagawaNumberTwo_of_ternary_nf`**, `massFormula_of_ternary_nf`, `siegelFormulaAt_of_ternary_nf` ($\tau = 2$, the
  mass formula in every rank $N \ge 4$, Siegel's formula in every rank $N \ge 5$, every totally real $F$), conditional on
  `TernaryTamagawaTwo F` and `RankFourUnitSiegel F`; `tamagawaNumberTwo_of_pureForm_nf` with the pure forms in place of the
  ternary input.

Sources: Weil 1982, §3.7, Thm. 3.7.1, p. 65 ($m = 3, 4$), and §4.5, p. 100 (Siegel's theorem and the induction).
-/
import QuadFormsKB.Tamagawa.LatticeChangeNF
import QuadFormsKB.Tamagawa.NonPIDEuler
import QuadFormsKB.Tamagawa.RatBridge

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices QuadForm HilbertModular QuatZeta LatChange

variable {F : Type} [Field F] [NumberField F]

/-! ### Elementary facts over a totally real field -/

section Basic

variable [IsTotallyReal F]

open scoped ComplexOrder in
theorem isTotallyPos_sq_nf {t : F} (ht : t ≠ 0) : IsTotallyPos (t ^ 2) := fun σ => by
  have hreal := NumberField.IsTotallyReal.complexEmbedding_isReal (K := F) σ.toRingHom
  have him : (σ t).im = 0 := by
    have := congrArg (fun φ : F →+* ℂ => φ t) (NumberField.ComplexEmbedding.isReal_iff.mp hreal)
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq] at this
    exact Complex.conj_eq_iff_im.mp this
  have hre : (σ t).re ≠ 0 := by
    intro h0
    exact (map_ne_zero σ).mpr ht (Complex.ext h0 him)
  rw [map_pow, Complex.lt_def]
  simp only [Complex.zero_re, Complex.zero_im, pow_two, Complex.mul_re, Complex.mul_im, him, mul_zero, sub_zero,
    zero_mul, add_zero]
  exact ⟨mul_self_pos.mpr hre, trivial⟩

open scoped ComplexOrder in
/-- $\langle 1\rangle\perp S$ is totally positive definite when $S$ is ($F$ totally real; no PID). -/
theorem isTotallyPosDef_splitForm_one_nf {n : ℕ} {S : QuadForm F n} (hS : IsTotallyPosDef S) :
    IsTotallyPosDef (splitForm 1 S) := by
  intro x hx
  rw [← Fin.cons_self_tail x, eval_splitForm_cons, one_mul, ← pow_two]
  by_cases ht : Fin.tail x = 0
  · have h0 : x 0 ≠ 0 := by
      intro h0; apply hx; rw [← Fin.cons_self_tail x, h0, ht]; ext i; refine Fin.cases ?_ (fun _ => ?_) i <;> simp
    rw [ht, show S.eval (0 : Fin n → F) = 0 by simp [QuadForm.evalIn]]
    simpa using isTotallyPos_sq_nf h0
  · intro σ
    rw [map_add]
    refine add_pos_of_nonneg_of_pos ?_ (hS _ ht σ)
    by_cases h0 : x 0 = 0
    · simp [h0]
    · exact (isTotallyPos_sq_nf h0 σ).le

theorem realEmb_one_pos (v : InfinitePlace F) : 0 < realEmb F v (algebraMap (𝓞 F) F 1) := by simp

end Basic

/-! ### Reduction to $\langle 1\rangle\perp Q_3$ and to diagonal forms (no PID) -/

section Diag

theorem diag_succ_compMat_eq {m : ℕ} (e : Fin (m + 1) → 𝓞 F) :
    (QuadForm.diag (Fin.cons 1 fun i => e 0 * e i.succ)).compMat
        (diagonal (Fin.cons (e 0) fun _ => (1 : 𝓞 F))) = e 0 • QuadForm.diag e := by
  ext i j
  congr 1
  rw [compMat_diagonal_coeff, smul_coeff, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [QuadForm.diag]
  · simp [QuadForm.diag, diagonal_apply_ne _ hij]

theorem diagonal_det_ne_zero {m : ℕ} {c : Fin m → 𝓞 F} (hc : ∀ i, c i ≠ 0) : (diagonal c).det ≠ 0 := by
  rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hc i

theorem isTotallyPosDef_of_compMat {n : ℕ} {S : QuadForm F n} {X : Matrix (Fin n) (Fin n) F} (hX : X.det ≠ 0)
    (h : IsTotallyPosDef (S.compMat X)) : IsTotallyPosDef S := by
  have e : S = (S.compMat X).compMat X⁻¹ := by
    rw [compMat_mul, mul_nonsing_inv _ (Ne.isUnit hX), compMat_one]
  rw [e]
  exact isTotallyPosDef_compMat_of_det h (isUnit_nonsing_inv_det X (Ne.isUnit hX)).ne_zero

/-- **Every quaternary $\tau$ is the $\tau$ of a diagonal form $\langle 1, b, c, d\rangle$** (any number field, no PID):
$Q_0\circ G = \langle e_0, \dots, e_3\rangle$ (`exists_compMat_eq_diag`) and
$\langle 1, e_0e_1, e_0e_2, e_0e_3\rangle\circ\mathrm{diag}(e_0, 1, 1, 1) = e_0\langle e_0, \dots, e_3\rangle$, so $\tau(Q_0) = \tau(\langle 1, b, c, d\rangle)$
by `tauSO_compMat_nf` and `tauSO_smul_compMat_nf`. Stated for every rank $m + 1 \ge 3$. -/
theorem tauSO_eq_tauSO_diag_one_nf {m : ℕ} (hm : 2 ≤ m) (Q₀ : QuadForm (𝓞 F) (m + 1)) (hQ₀ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    ∃ b : Fin m → 𝓞 F, (∀ i, b i ≠ 0) ∧
      IsTotallyPosDef ((QuadForm.diag (Fin.cons 1 b : Fin (m + 1) → 𝓞 F)).map (algebraMap (𝓞 F) F)) ∧
      tauSO Q₀ = tauSO (QuadForm.diag (Fin.cons 1 b : Fin (m + 1) → 𝓞 F)) := by
  obtain ⟨G, hG, e, he, hGe⟩ := exists_compMat_eq_diag Q₀ hQ₀
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  have hpdD : IsTotallyPosDef ((QuadForm.diag e).map (algebraMap (𝓞 F) F)) := by
    rw [← hGe, ← map_compMat]; exact isTotallyPosDef_compMat_of_det hpd hGF
  have hQD : (QuadForm.diag e).Nondegenerate := by rw [← hGe]; exact nondegenerate_compMat_of_det hQ₀ hG
  set b : Fin m → 𝓞 F := fun i => e 0 * e i.succ
  set Q₁ : QuadForm (𝓞 F) (m + 1) := QuadForm.diag (Fin.cons 1 b)
  set D : Matrix (Fin (m + 1)) (Fin (m + 1)) (𝓞 F) := diagonal (Fin.cons (e 0) fun _ => (1 : 𝓞 F))
  have hD : D.det ≠ 0 := diagonal_det_ne_zero (fun i => by
    refine Fin.cases ?_ (fun _ => ?_) i <;> simp [he 0])
  have hDF : (D.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hD
  have hQ₁D : Q₁.compMat D = e 0 • QuadForm.diag e := diag_succ_compMat_eq e
  have he0 : IsTotallyPos (((e 0 : 𝓞 F)) : F) := by
    have := hpdD (Pi.single 0 1) (by simp)
    rw [eval_single] at this
    simpa [QuadForm.map, QuadForm.diag] using this
  have hpdE : IsTotallyPosDef ((e 0 • QuadForm.diag e).map (algebraMap (𝓞 F) F)) := by
    intro x hx
    have h1 : ((e 0 • QuadForm.diag e).map (algebraMap (𝓞 F) F)).eval x =
        (e 0 : F) * ((QuadForm.diag e).map (algebraMap (𝓞 F) F)).eval x := by
      rw [← eval_smul_form]; congr 1
    rw [h1]; exact isTotallyPos_mul he0 (hpdD x hx)
  have hpd₁ : IsTotallyPosDef (Q₁.map (algebraMap (𝓞 F) F)) := by
    refine isTotallyPosDef_of_compMat hDF ?_
    rw [map_compMat, hQ₁D]; exact hpdE
  have hQ₁ : Q₁.Nondegenerate := nondegenerate_of_map hpd₁.nondegenerate
  refine ⟨b, fun i => mul_ne_zero (he 0) (he i.succ), hpd₁, ?_⟩
  have h1 := tauSO_compMat_nf (by omega) (by omega) Q₁ hQ₁ hpd₁ D hD
  rw [hQ₁D] at h1
  have h2 := tauSO_smul_compMat_nf (by omega) (by omega) (QuadForm.diag e) hQD hpdD (he 0) 1 (by simp)
    (by rw [compMat_one]; exact hpdE)
  rw [compMat_one] at h2
  have h3 := tauSO_compMat_nf (by omega) (by omega) Q₀ hQ₀ hpd G hG
  rw [hGe] at h3
  rw [← h3, ← h2, ← h1]

/-- **`QuaternaryTamagawaTwo F` from the diagonal forms $\langle 1, b, c, d\rangle$** (any number field, no PID). -/
@[kb "weil1982" "§3.7, Thm. 3.7.1 (m = 4), p. 65; τ is a similarity invariant (§2.4)"]
theorem quaternaryTamagawaTwo_of_diag_nf
    (h : ∀ b : Fin 3 → 𝓞 F, (∀ i, b i ≠ 0) →
      IsTotallyPosDef (formF (QuadForm.diag (Fin.cons 1 b : Fin 4 → 𝓞 F))) →
      TamagawaNumberTwo (QuadForm.diag (Fin.cons 1 b : Fin 4 → 𝓞 F))) : QuaternaryTamagawaTwo F :=
  ⟨fun Q₀ hpd => by
    obtain ⟨b, hb, hpd', he⟩ := tauSO_eq_tauSO_diag_one_nf (m := 3) (by norm_num) Q₀
      (nondegenerate_of_map hpd.nondegenerate) hpd
    unfold TamagawaNumberTwo; rw [he]; exact h b hb hpd'⟩

theorem diag_cons_one_eq_splitForm {m : ℕ} (b : Fin m → 𝓞 F) :
    QuadForm.diag (Fin.cons 1 b : Fin (m + 1) → 𝓞 F) = splitForm 1 (QuadForm.diag b) := by
  rw [diag_eq_splitForm]; rfl

/-- **`QuaternaryTamagawaTwo F` from the forms $\langle 1\rangle\perp Q_3$** (any number field, no PID). -/
@[kb "weil1982" "§3.7, Thm. 3.7.1 (m = 4), p. 65"]
theorem quaternaryTamagawaTwo_of_unitSplit_nf
    (h : ∀ Q₃ : QuadForm (𝓞 F) 3, IsTotallyPosDef (formF (splitForm 1 Q₃)) → TamagawaNumberTwo (splitForm 1 Q₃)) :
    QuaternaryTamagawaTwo F :=
  quaternaryTamagawaTwo_of_diag_nf fun b _ hpd => by
    rw [diag_cons_one_eq_splitForm] at hpd ⊢; exact h _ hpd

end Diag

/-! ### Ternary ⟺ quaternary, given rank-4 Siegel for the number 1 -/

section Ternary

/-- **Input (rank-4 Siegel for the number $1$):** for every ternary $Q_3$ over $\mathcal O_F$ with $\langle 1\rangle\perp Q_3$ totally positive
definite, Siegel's formula for representations of $1$ by the genus of $\mathcal O_F\perp\mathcal O_F^3$:
$\mathrm{repMass}(\langle 1\rangle\perp Q_3, 1) = \mathrm{Mass}\cdot S(L, 1)$ (`SiegelFormulaAt`; Siegel 1935, Hauptsatz, $n = 4$).

Field:
- `siegel`: the statement above.

*Status.* A theorem for $\mathcal O_F$ a PID with $[F:\mathbb Q] \ge 2$ (via Hilbert modular forms, `rankFourUnitSiegel_of_pid`) and for $F = \mathbb Q$
(through the bridge, `rankFourUnitSiegel_rat`). For $h_F > 1$ Hilbert modular forms prove Siegel's formula
only in rank $\ge 6$ (`HilbertModular.siegelFormulaAt'`, given `PrincipalPrimeSupply F`); rank 4 there needs prime
counting among principal primes (`HeckeVanishingNP`). It is Siegel's formula (a statement about representation
numbers), not a statement about $\tau$: it is not equivalent to `QuaternaryTamagawaTwo F` or to
`TernaryTamagawaTwo F`, which it is used to compare. -/
@[kb "siegel1935" "Hauptsatz, n = 4, m = 1 (rank-4 Siegel for the number 1; input for h_F > 1) [unverified]"]
structure RankFourUnitSiegel (F : Type) [Field F] [NumberField F] : Prop where
  siegel : ∀ Q₃ : QuadForm (𝓞 F) 3, IsTotallyPosDef (formF (splitForm 1 Q₃)) → SiegelFormulaAt (splitForm 1 Q₃) 1

variable [IsTotallyReal F]

/-- `RankFourUnitSiegel F` holds for $\mathcal O_F$ a PID of degree $\ge 2$ (via Hilbert modular forms,
`siegelFormulaAt_of_pid_four`). -/
theorem rankFourUnitSiegel_of_pid [IsPrincipalIdealRing (𝓞 F)] (hd : 2 ≤ Fintype.card (InfinitePlace F)) :
    RankFourUnitSiegel F :=
  ⟨fun _ hpd => siegelFormulaAt_of_pid_four (n := 4) hpd rfl hd realEmb_one_pos⟩

/-- `RankFourUnitSiegel ℚ` holds (through the bridge, `RatBridge.siegelFormulaAt_rat_four`). -/
theorem rankFourUnitSiegel_rat : RankFourUnitSiegel ℚ :=
  ⟨fun _ hpd => RatBridge.siegelFormulaAt_rat_four hpd realEmb_one_pos⟩

/-- **$\tau(SO_4) = 2$ from $\tau(SO_3) = 2$ over every totally real field**, given rank-4 Siegel for the number $1$:
$\tau(\langle 1\rangle\perp Q_3) = 2$ by `tamagawaNumberTwo_four_of_three_of_siegel` (no PID), and every quaternary $\tau$
is such a $\tau$ (`quaternaryTamagawaTwo_of_unitSplit_nf`, the non-PID change of lattice). -/
@[kb "weil1982" "§3.7, pp. 62-65; Thm. 3.7.1 (m = 4), p. 65; any class number, given rank-4 Siegel for m = 1"]
theorem quaternaryTamagawaTwo_of_ternary_nf (hT : TernaryTamagawaTwo F) (hS : RankFourUnitSiegel F) :
    QuaternaryTamagawaTwo F :=
  quaternaryTamagawaTwo_of_unitSplit_nf fun Q₃ hpd => by
    have hpd₀ := hpd
    rw [formF, map_splitForm_alg] at hpd₀
    have hpd' := isTotallyPosDef_of_splitForm hpd₀
    have hLi' := isIntegral_of_splitForm (m := algebraMap (𝓞 F) F 1) (Q' := Q₃.map (algebraMap (𝓞 F) F))
      (by rw [← map_splitForm_alg]; exact isIntegral_std _)
    exact tamagawaNumberTwo_four_of_three_of_siegel realEmb_one_pos Q₃ hpd (isIntegral_std _) (hS.siegel Q₃ hpd)
      (hT.tau_eq_two Q₃ (nondegenerate_of_map hpd'.nondegenerate) hpd' hLi')

/-- **$\tau(SO_3) = 2$ from $\tau(SO_4) = 2$ over every totally real field**, given rank-4 Siegel for the number $1$
(`tamagawaNumberTwo_three_of_four_of_siegel` at $\langle 1\rangle\perp Q_3$). -/
@[kb "weil1982" "Thm. 3.7.1 (m = 3 from m = 4), p. 65; any class number, given rank-4 Siegel for m = 1"]
theorem ternaryTamagawaTwo_of_quaternary_nf (h4 : QuaternaryTamagawaTwo F) (hS : RankFourUnitSiegel F) :
    TernaryTamagawaTwo F :=
  ⟨fun Q₃ _ hpd' _ => by
    have hpd : IsTotallyPosDef (formF (splitForm 1 Q₃)) := by
      rw [formF, map_splitForm_alg, map_one]; exact isTotallyPosDef_splitForm_one_nf hpd'
    exact tamagawaNumberTwo_three_of_four_of_siegel realEmb_one_pos Q₃ hpd (isIntegral_std _) (hS.siegel Q₃ hpd)
      (h4.tau_eq_two _ hpd)⟩

/-- **The ternary and quaternary inputs are equivalent over every totally real field** (any class number), given rank-4
Siegel for the number $1$. For $\mathcal O_F$ a PID of degree $\ge 2$ and for $\mathbb Q$ the Siegel input is a theorem. -/
@[kb "weil1982" "Thm. 3.7.1, p. 65 (m = 3 ⟺ m = 4), any class number, given rank-4 Siegel for m = 1"]
theorem ternaryTamagawaTwo_iff_quaternary_nf (hS : RankFourUnitSiegel F) :
    TernaryTamagawaTwo F ↔ QuaternaryTamagawaTwo F :=
  ⟨fun hT => quaternaryTamagawaTwo_of_ternary_nf hT hS, fun h4 => ternaryTamagawaTwo_of_quaternary_nf h4 hS⟩

/-- **$\tau = 2$ in every rank $N \ge 4$, every totally real field**, from the ternary input and rank-4 Siegel for the number $1$. -/
@[kb "weil1982" "Thm. 3.7.1 and Thm. 4.5.1, p. 109, any class number (given τ(SO_3) = 2 and rank-4 Siegel for m = 1)"]
theorem tamagawaNumberTwo_of_ternary_nf (hT : TernaryTamagawaTwo F) (hS : RankFourUnitSiegel F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_of_quaternary_nf (quaternaryTamagawaTwo_of_ternary_nf hT hS) hN Q₀ hpd

/-- **The mass formula in every rank $N \ge 4$, every totally real field**, same inputs. -/
@[kb "weil1982" "Thm. 4.5.1, p. 109; mass formula; any class number (given τ(SO_3) = 2 and rank-4 Siegel for m = 1)"]
theorem massFormula_of_ternary_nf (hT : TernaryTamagawaTwo F) (hS : RankFourUnitSiegel F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_of_quaternary_nf (quaternaryTamagawaTwo_of_ternary_nf hT hS) hN Q₀ hpd

/-- **Siegel's formula for numbers in every rank $N \ge 5$, every totally real field**, same inputs. -/
@[kb "weil1982" "§4.5, p. 100; Thm 4.5.1, p. 109; any class number (given τ(SO_3) = 2 and rank-4 Siegel for m = 1)"]
theorem siegelFormulaAt_of_ternary_nf (hT : TernaryTamagawaTwo F) (hS : RankFourUnitSiegel F) {n : ℕ} (hn : 4 ≤ n)
    (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_of_quaternary_nf (quaternaryTamagawaTwo_of_ternary_nf hT hS) hn Q₀ hpd hm

/-- **The mass formula for the genus of an arbitrary lattice (any Steinitz class), every rank $N \ge 4$, every totally real
field**, given `QuaternaryTamagawaTwo F`: $\mathrm{Mass}(L) = \mu_{\mathrm{Tam}}(K_{SO}(L))^{-1}$ for every lattice $L$ on
$(F^N, Q_0)$ integral for $Q_0$. -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula), arbitrary lattice, any class number (given τ(SO_4) = 2) [unverified]"]
theorem massFormula_lat_of_quaternary_nf (h4 : QuaternaryTamagawaTwo F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F N) (hLi : IsIntegral (formF Q₀) L.1) :
    mass (formF Q₀) L = (tamagawaKLat Q₀ L)⁻¹ :=
  massFormula_lat_nf Q₀ (nondegenerate_of_map hpd.nondegenerate) (by omega) hpd
    (tamagawaNumberTwo_of_quaternary_nf h4 hN Q₀ hpd) L hLi

end Ternary

/-! ### The ternary input reduces to the pure quaternion forms (no PID) -/

section Pure

variable [IsTotallyReal F]

/-- **$\tau(Q_0') = \tau(\langle -a,-b,ab\rangle)$ over every number field** (the version of `tauSO_eq_tauSO_pureFormO` without the PID). -/
theorem tauSO_eq_tauSO_pureFormO_nf (Q₀' : QuadForm (𝓞 F) 3) (hQ : Q₀'.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀'.map (algebraMap (𝓞 F) F))) :
    ∃ a b : 𝓞 F, a ≠ 0 ∧ b ≠ 0 ∧ IsTotallyPosDef ((pureFormO a b).map (algebraMap (𝓞 F) F)) ∧
      tauSO Q₀' = tauSO (pureFormO a b) := by
  obtain ⟨G, hG, e, he, hGe⟩ := exists_compMat_eq_diag Q₀' hQ
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  have hpdD : IsTotallyPosDef ((QuadForm.diag e).map (algebraMap (𝓞 F) F)) := by
    rw [← hGe, ← map_compMat]
    exact isTotallyPosDef_compMat_of_det hpd hGF
  have hepos : ∀ i, IsTotallyPos ((e i : 𝓞 F) : F) := fun i => by
    have := hpdD (Pi.single i 1) (by simp)
    rw [eval_single] at this
    simpa [QuadForm.map, QuadForm.diag] using this
  set cv : Fin 3 → 𝓞 F := ![1, 1, e 0 * e 1]
  have hcv : ∀ a, cv a ≠ 0 := by
    intro a; fin_cases a <;> simp [cv, he 0, he 1]
  set c' := e 0 * e 1 * e 2
  have hc' : c' ≠ 0 := mul_ne_zero (mul_ne_zero (he 0) (he 1)) (he 2)
  have hpdP : IsTotallyPosDef ((c' • (QuadForm.diag e).compMat (diagonal cv)).map (algebraMap (𝓞 F) F)) := by
    rw [map_smul_compMat_diagonal]
    intro x hx
    rw [eval_smul_form]
    refine isTotallyPos_mul ?_ ?_
    · show IsTotallyPos (((e 0 * e 1 * e 2 : 𝓞 F)) : F)
      push_cast
      exact isTotallyPos_mul (isTotallyPos_mul (hepos 0) (hepos 1)) (hepos 2)
    · have hD : (diagonal fun a => algebraMap (𝓞 F) F (cv a)).det ≠ 0 := by
        rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.mpr fun a _ => (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (hcv a)
      exact isTotallyPosDef_compMat_of_det hpdD hD x hx
  refine ⟨-(e 0 ^ 2 * e 1 * e 2), -(e 0 * e 1 ^ 2 * e 2), ?_, ?_, ?_, ?_⟩
  · exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (he 0)) (he 1)) (he 2))
  · exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (he 0) (pow_ne_zero _ (he 1))) (he 2))
  · rw [← smul_diag_compMat_eq_pureFormO]; exact hpdP
  · have h1 := tauSO_compMat_nf (by norm_num) (by norm_num) Q₀' hQ hpd G hG
    rw [hGe] at h1
    have hQD : (QuadForm.diag e).Nondegenerate := by
      rw [← hGe]; exact nondegenerate_compMat_of_det hQ hG
    rw [← h1, ← smul_diag_compMat_eq_pureFormO, tauSO_smul_compMat_diagonal (by norm_num) (by norm_num) _ hQD
      hpdD hc' cv hcv hpdP]

/-- **The ternary input reduces to the pure quaternion forms over every totally real field** (the version of
`ternaryTamagawaTwo_of_pureForm` without the PID): if $\tau(\langle -a,-b,ab\rangle) = 2$ for all $a, b \in \mathcal O_F\setminus0$ with
$\langle -a,-b,ab\rangle$ totally positive definite, then `TernaryTamagawaTwo F`. -/
@[kb "weil1982" "§3.7(a), p. 62-63 (every ternary space is similar to (D^0, nrd)); any class number"]
theorem ternaryTamagawaTwo_of_pureForm_nf
    (h : ∀ a b : 𝓞 F, a ≠ 0 → b ≠ 0 → IsTotallyPosDef ((pureFormO a b).map (algebraMap (𝓞 F) F)) →
      TamagawaNumberTwo (pureFormO a b)) : TernaryTamagawaTwo F :=
  ⟨fun Q₀' hQ hpd _ => by
    obtain ⟨a, b, ha, hb, hpd', he⟩ := tauSO_eq_tauSO_pureFormO_nf Q₀' hQ hpd
    unfold TamagawaNumberTwo; rw [he]; exact h a b ha hb hpd'⟩

/-- **$\tau = 2$ in every rank $N \ge 4$, every totally real field, from the pure quaternion forms** and rank-4 Siegel for the
number $1$: the two remaining inputs for $h_F > 1$ are $\tau(\langle -a,-b,ab\rangle) = 2$ (the standard orders of the totally definite
quaternion algebras $(a,b)_F$; stage 2, the quaternion route) and `RankFourUnitSiegel F`. -/
@[kb "weil1982" "§3.7, Thm. 3.7.1; Thm. 4.5.1, p. 109; any class number (given τ = 2 for ⟨-a,-b,ab⟩ and rank-4 Siegel for m = 1)"]
theorem tamagawaNumberTwo_of_pureForm_nf
    (h : ∀ a b : 𝓞 F, a ≠ 0 → b ≠ 0 → IsTotallyPosDef ((pureFormO a b).map (algebraMap (𝓞 F) F)) →
      TamagawaNumberTwo (pureFormO a b)) (hS : RankFourUnitSiegel F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_of_ternary_nf (ternaryTamagawaTwo_of_pureForm_nf h) hS hN Q₀ hpd

end Pure

end QuadFormsKB.Tamagawa
