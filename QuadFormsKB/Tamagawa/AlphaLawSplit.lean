/-
# The $\alpha$ transformation law: definition and the split step

**Layer:** the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime (every residue characteristic,
dyadic included); local forms given by integral models $Q_o$ over $\mathfrak o_\mathfrak p$.

**Defines** `AlphaLawAt v Q_o P hP`, the **$\alpha$ transformation law** for the pair of lattices $P\,\mathfrak o_\mathfrak p^N \subseteq \mathfrak o_\mathfrak p^N$ of
$(F_\mathfrak p^N, Q_o)$:
$$r\big(K(P\mathfrak o_\mathfrak p^N),\,K(\mathfrak o_\mathfrak p^N)\big)\cdot\beta_\mathfrak p(Q_o, Q_o) = \beta_\mathfrak p(Q_o\circ P, Q_o\circ P)\cdot\|\det P\|_\mathfrak p^{N+1},$$
$K(\Lambda) = O(\Lambda)$ the lattice stabilizers in $O(Q_o)(F_\mathfrak p)$ (`KL`), $r(A, B) = [A : A\cap B]/[B : A\cap B]$ (`relRatio`).
(Weil's normalization $\mu(O(\Lambda)) \propto \alpha(\Lambda)\,|\det\Lambda|^{(N+1)/2}$ in finite form; Weil 1982, §2.4 and §3.4
[unverified].)

**Proves**
* `card_ker_redMat_eq` : $|\ker(P \bmod \varpi^k)| = \|\det P\|^{-1}$ for $\det P \mid \varpi^k$;
* `exists_blockGL_eq` : an isometry of $\langle m\rangle\perp Q''$ over $F_\mathfrak p$ fixing $e_0$ is $\mathrm{diag}(1, g'')$;
* `relIndex_stab_e₀` : the stabilizers of $e_0$ in $K(\langle m\rangle\perp\Lambda_i'')$ compare as $K(\Lambda_i'')$;
* **`alphaLaw_split`** (the split step): the law for $(Q'', P'')$ in rank $n$ gives the law for
  $(\langle m\rangle\perp Q'',\ \mathrm{diag}(1, P''))$ in rank $n+1$, at every prime. *Proof:* REL (`rel_local`) at $y = e_0$, the orbit
  of $e_0$ (`card_orbitSet_eq_nearCount`) and the fibration count (`repCountForm_splitForm_orbit`) in both lattices.

Sources: Weil 1982, §3.4 [unverified]; Hanke 2004, §3, Def. 3.1 and the maps $\pi_Z$, $\pi_{B'}$, $\pi_{B''}$, pp. 358–361. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.AlphaLaw
import QuadFormsKB.Tamagawa.OrbitalEuler

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices QuadForm LocalDensity LocalDensity.DVR

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-! ### The law -/

section Def

variable {N : ℕ}

/-- **The $\alpha$ transformation law for $P\,\mathfrak o_\mathfrak p^N \subseteq \mathfrak o_\mathfrak p^N$** (Weil 1982, §3.4 [unverified]):
$$r\big(K(P\mathfrak o_\mathfrak p^N), K(\mathfrak o_\mathfrak p^N)\big)\,\beta(Q_o) = \beta(Q_o\circ P)\,\|\det P\|^{N+1},$$
$\beta(Q) = \beta_\mathfrak p(Q, Q)$ (`DVR.localDensityForm`), $K$ = `KL` in $O(Q_o)(F_\mathfrak p)$, $r$ = `relRatio`. -/
@[kb "weil1982" "§3.4 (Haar measures of lattice stabilizers, finite form) [unverified]"]
def AlphaLawAt (Qo : QuadForm 𝔬 N) (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) : Prop :=
  relRatio (KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v)))
      (KL v (Qo.map (algebraMap 𝔬 Fv)) (std v)) * localDensityForm Qo Qo (NF.π v) =
    localDensityForm (Qo.compMat P) (Qo.compMat P) (NF.π v) * ‖(((P.det : 𝔬)) : Fv)‖ ^ (N + 1)

/-- $|\ker(P \bmod \varpi^k)| = \|\det P\|^{-1}$ when $\det P \mid \varpi^k$. -/
theorem card_ker_redMat_eq (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) {k : ℕ} (hk : P.det ∣ NF.π v ^ k) :
    (Nat.card (redMat (NF.π v) k P).ker : ℝ) = ‖(((P.det : 𝔬)) : Fv)‖⁻¹ := by
  have hπ := NF.irreducible_π v
  rw [card_ker_redMat hπ P (exists_mulVec_eq_smul P hk), card_quot_range hπ P hP]
  obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hP
  rw [card_quot_span_eq hπ he he', norm_coe_of_pow_dvd v he he', inv_inv]
  push_cast; rfl

/-- $\beta_\mathfrak p(Q, Q) > 0$ for nondegenerate $Q$ (the identity is a solution at every level). -/
theorem localDensityForm_self_pos' (Qo : QuadForm 𝔬 N) (hQ : Qo.Nondegenerate) :
    0 < localDensityForm Qo Qo (NF.π v) := by
  obtain ⟨k, hk⟩ := (localDensityForm_self_eventually_eq Qo hQ (NF.π v) (NF.irreducible_π v)).exists
  rw [← hk]
  have hq : (0 : ℝ) < q 𝔬 := Nat.cast_pos.mpr q_pos
  refine div_pos ?_ (pow_pos hq _)
  have : 0 < repCountForm Qo Qo (NF.π v) k := by
    have := finite_quot_pow (NF.π v) (NF.irreducible_π v) k
    unfold repCountForm
    refine Nat.card_pos_iff.mpr ⟨⟨⟨1, by rw [compMat_one]⟩⟩, ?_⟩
    infer_instance
  exact_mod_cast this

end Def

/-! ### Split lattices -/

section SplitLemmas

variable {n : ℕ}

/-- **The stabilizer of $e_0$ in $O(\langle m\rangle\perp Q'')(F_\mathfrak p)$ is $\mathrm{diag}(1, O(Q''))$** (local forms; as
`exists_orthEmb_eq`). -/
theorem exists_blockGL_eq {m : Fv} (hm : m ≠ 0) (Q'' : QuadForm Fv n) (g : GL (Fin (n + 1)) Fv)
    (hg : (splitForm m Q'').compMat g.val = splitForm m Q'') (he : g.val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀) :
    ∃ g'' : GL (Fin n) Fv, Q''.compMat g''.val = Q'' ∧ blockGL g'' = g := by
  set A := g.val with hA
  have hγo := congrArg QuadForm.hessian hg
  rw [hessian_compMat, hessian_splitForm] at hγo
  set c := (2 : Fv) * m
  have hc : c ≠ 0 := mul_ne_zero two_ne_zero hm
  set H' := Q''.hessian
  have hcol : ∀ i, A i 0 = (e₀ : Fin (n + 1) → Fv) i := by
    intro i
    have := congrFun he i
    rw [e₀_eq_single, mulVec_single_one] at this
    rw [e₀_eq_single]; exact this
  have hrow : ∀ j, A 0 j = (e₀ : Fin (n + 1) → Fv) j := by
    have h1 : Pi.single 0 1 ᵥ* (Aᵀ * cornerMat c H' * A) = Pi.single 0 1 ᵥ* cornerMat c H' := by rw [hγo]
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, ← e₀_eq_single, he, e₀_eq_single] at h1
    have h2 : Pi.single (0 : Fin (n + 1)) (1 : Fv) ᵥ* cornerMat c H' = c • Pi.single 0 1 := by
      rw [single_one_vecMul]
      ext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.row]
    rw [h2, smul_vecMul, single_one_vecMul] at h1
    intro j
    have := congrFun h1 j
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.row] at this
    rw [e₀_eq_single]
    exact mul_left_cancel₀ hc this
  set g' := A.submatrix Fin.succ Fin.succ
  have hAg : A = cornerMat 1 g' := by
    refine Matrix.ext fun i j => ?_
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hcol 0
    · simpa [Fin.succ_ne_zero] using hrow j.succ
    · simpa [Fin.succ_ne_zero] using hcol i.succ
    · rfl
  have hdet : g'.det ≠ 0 := by
    have h := (g.isUnit.map Matrix.detMonoidHom).ne_zero
    rw [Matrix.coe_detMonoidHom, ← hA, hAg, det_cornerMat, one_mul] at h
    exact h
  let gGL := Matrix.GeneralLinearGroup.mkOfDetNeZero g' hdet
  refine ⟨gGL, ?_, Units.ext (by rw [blockGL_val]; exact hAg.symm)⟩
  rw [hAg, compMat_cornerMat] at hg
  exact splitForm_injective_right hg

/-- $\mathrm{diag}(1, g'')$ stabilizes $\mathrm{diag}(1, h'')\,\mathfrak o_\mathfrak p^{n+1}$ in $O(\langle m\rangle\perp Q'')$ iff $g''$ stabilizes
$h''\mathfrak o_\mathfrak p^n$ in $O(Q'')$. -/
theorem blockGL_mem_KL_iff (m : Fv) (Q'' : QuadForm Fv n) (g'' h'' : GL (Fin n) Fv) :
    blockGL g'' ∈ KL v (splitForm m Q'') (locAct v (blockGL h'') (std v)) ↔
      g'' ∈ KL v Q'' (locAct v h'' (std v)) := by
  rw [mem_KL, mem_KL, blockGL_val, compMat_cornerMat]
  refine and_congr ⟨splitForm_injective_right, fun h => by rw [h]⟩ ?_
  have e1 : ∀ {k : ℕ} (x y : GL (Fin k) Fv), locAct v x (locAct v y (std v)) = locAct v y (std v) ↔
      locAct v (y⁻¹ * x * y) (std v) = std v := by
    intro k x y
    rw [locAct_mul, locAct_mul]
    constructor
    · intro h; rw [h, locAct_inv_locAct]
    · intro h
      have := congrArg (locAct v y) h
      rwa [← locAct_mul, mul_inv_cancel, locAct_one] at this
  rw [e1, e1, ← map_inv, ← map_mul, ← map_mul, locAct_blockGL_std_iff]

theorem glOf_cornerMat (P'' : Matrix (Fin n) (Fin n) 𝔬) (hP'' : P''.det ≠ 0) (hP : (cornerMat 1 P'').det ≠ 0) :
    glOf v (cornerMat 1 P'') hP = blockGL (glOf v P'' hP'') := by
  apply Units.ext
  rw [glOf_val, blockGL_val, glOf_val, cornerMat_map, map_one]

/-- **Relative indices through an embedding**: if $\iota$ embeds $K_1''$ onto the subgroup $S$ of $K_1$ and $\iota^{-1}(K_2) \cap K_1'' = K_2''\cap K_1''$,
then $[S : S \cap K_2] = [K_1'' : K_1''\cap K_2'']$. -/
theorem relIndex_stab_eq {G G' : Type*} [Group G] [Group G'] (K₁ K₂ : Subgroup G) (S : Subgroup K₁)
    (ι : G' →* G) (K₁'' K₂'' : Subgroup G') (hS : S.map K₁.subtype = K₁''.map ι)
    (h2 : ∀ g ∈ K₁'', ι g ∈ K₂ ↔ g ∈ K₂'') :
    (K₂.subgroupOf K₁).relIndex S = K₂''.relIndex K₁'' := by
  rw [← Subgroup.relIndex_map_map_of_injective _ _ K₁.subtype_injective, Subgroup.subgroupOf_map_subtype, hS,
    ← Subgroup.relIndex_comap, ← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right K₂'']
  congr 1
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_comap]
  constructor
  · rintro ⟨⟨h₂, -⟩, h₁⟩; exact ⟨(h2 g h₁).mp h₂, h₁⟩
  · rintro ⟨h₂, h₁⟩
    have hι1 : ι g ∈ K₁ := by
      have : ι g ∈ K₁''.map ι := ⟨g, h₁, rfl⟩
      rw [← hS] at this
      obtain ⟨κ, -, hκ⟩ := this
      rw [← hκ]; exact κ.2
    exact ⟨⟨(h2 g h₁).mpr h₂, hι1⟩, h₁⟩

/-- **The stabilizer of $e_0$ in $K(\mathrm{diag}(1, h'')\mathfrak o_\mathfrak p^{n+1})$** is $\mathrm{diag}(1, K(h''\mathfrak o_\mathfrak p^n))$, for any
representation $\rho$ whose fixed points of $e_0$ are those of $K$. -/
theorem stab_e₀_map {m : Fv} (hm : m ≠ 0) (Q'' : QuadForm Fv n) (h'' : GL (Fin n) Fv)
    (ρ : KL v (splitForm m Q'') (locAct v (blockGL h'') (std v)) →* Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬)
    (hρ : ∀ κ, ρ κ *ᵥ (e₀ : Fin (n + 1) → 𝔬) = e₀ ↔
      (κ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀) :
    (stabOf ρ e₀).map (KL v (splitForm m Q'') (locAct v (blockGL h'') (std v))).subtype =
      (KL v Q'' (locAct v h'' (std v))).map blockGL := by
  ext g
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    have hκ' := (hρ κ).mp hκ
    obtain ⟨g'', hg''Q, hg''⟩ := exists_blockGL_eq v hm Q'' κ ((mem_KL v).mp κ.2).1 hκ'
    refine ⟨g'', ?_, hg''⟩
    show g'' ∈ KL v Q'' (locAct v h'' (std v))
    rw [← blockGL_mem_KL_iff v m, hg'']
    exact κ.2
  · rintro ⟨g'', hg'', rfl⟩
    have hmem := (blockGL_mem_KL_iff v m Q'' g'' h'').mpr hg''
    exact ⟨⟨_, hmem⟩, (hρ ⟨_, hmem⟩).mpr (blockGL_mulVec_e₀ g''), rfl⟩

theorem stab_e₀_map' {m' : Fv} (hm' : m' ≠ 0) {Qv : QuadForm Fv (n + 1)} {Q''v : QuadForm Fv n}
    (hQv : Qv = splitForm m' Q''v) {Λ : Submodule 𝔬 (Fin (n + 1) → Fv)} {h'' : GL (Fin n) Fv}
    (hΛ : Λ = locAct v (blockGL h'') (std v)) (ρ : KL v Qv Λ →* Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬)
    (hρ : ∀ κ, ρ κ *ᵥ (e₀ : Fin (n + 1) → 𝔬) = e₀ ↔
      (κ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀) :
    (stabOf ρ e₀).map (KL v Qv Λ).subtype = (KL v Q''v (locAct v h'' (std v))).map blockGL := by
  subst hQv; subst hΛ
  exact stab_e₀_map v hm' Q''v h'' ρ hρ

theorem coe_e₀_o' : (fun i => (((e₀ : Fin (n + 1) → 𝔬) i : 𝔬) : Fv)) = (e₀ : Fin (n + 1) → Fv) := by
  funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem repAt_mulVec_e₀_iff {Qv : QuadForm Fv (n + 1)} (h : GL (Fin (n + 1)) Fv)
    (hh : h.val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀) (κ : KL v Qv (locAct v h (std v))) :
    repAt v Qv h κ *ᵥ (e₀ : Fin (n + 1) → 𝔬) = e₀ ↔
      (κ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
  have hinj := coe_o_injective v (N := n + 1)
  rw [← hinj.eq_iff]
  rw [coe_mulVec_o, repAt_map, coe_e₀_o']
  simp only [Units.val_mul, ← mulVec_mulVec, hh]
  constructor
  · intro h1
    have := congrArg (h.val *ᵥ ·) h1
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, hh] at this
  · intro h1
    rw [h1]
    have : h⁻¹.val *ᵥ (h.val *ᵥ (e₀ : Fin (n + 1) → Fv)) = e₀ := by
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rwa [hh] at this

theorem repStd_mulVec_e₀_iff {Qv : QuadForm Fv (n + 1)} (κ : KL v Qv (std v)) :
    repStd v Qv κ *ᵥ (e₀ : Fin (n + 1) → 𝔬) = e₀ ↔
      (κ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
  have hinj := coe_o_injective v (N := n + 1)
  rw [← hinj.eq_iff]
  rw [coe_mulVec_o, repStd_map, coe_e₀_o']

theorem dvd_pow_ord {x : 𝔬} (hx : x ≠ 0) : ∃ c : ℕ, x ∣ NF.π v ^ c := by
  obtain ⟨c, u, rfl, hu⟩ := dvr_eq_pow_mul_unit (NF.irreducible_π v) hx
  exact ⟨c, ⟨(hu.unit⁻¹ : 𝔬ˣ), by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]⟩⟩

end SplitLemmas

/-! ### The split step -/

section SplitStep

variable {n : ℕ}

/-- **The split step of the $\alpha$ transformation law** (every prime, dyadic included): the law for $(Q'', P'')$ in rank $n$
implies the law for $(\langle m\rangle\perp Q'',\ \mathrm{diag}(1, P''))$ in rank $n + 1$ ($m \ne 0$). *Proof:* REL at $y = e_0$
(`rel_local`); the stabilizers of $e_0$ are $\mathrm{diag}(1, K(\Lambda_i''))$ (`stab_e₀_map`, `relIndex_stab_eq`); the orbits of $e_0$ are the
orbits mod $\varpi^k$ (`card_orbitSet_eq_nearCount`), counted by the fibration (`repCountForm_splitForm_orbit`); the index is
$\|\det P''\|^{-1}$ (`card_ker_redMat_eq`). -/
@[kb "weil1982" "§3.4 (the fibration over the orbit of e₀ and lattice change) [unverified]"]
theorem alphaLaw_split (Q'' : QuadForm 𝔬 n) (hQ'' : Q''.Nondegenerate) {m : 𝔬} (hm : m ≠ 0)
    (P'' : Matrix (Fin n) (Fin n) 𝔬) (hP'' : P''.det ≠ 0) (hP : (cornerMat 1 P'').det ≠ 0)
    (ih : AlphaLawAt v Q'' P'' hP'') : AlphaLawAt v (splitForm m Q'') (cornerMat 1 P'') hP := by
  classical
  have hπ := NF.irreducible_π v
  have h2 := NF.two_ne_zero' v
  set Qo := splitForm m Q''
  set P := cornerMat 1 P''
  set Q₁'' := Q''.compMat P''
  have hQ₁ : Qo.compMat P = splitForm m Q₁'' := compMat_cornerMat m Q'' P''
  have hdetP : P.det = P''.det := by rw [det_cornerMat, one_mul]
  have hQo : Qo.Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]; exact mul_ne_zero (mul_ne_zero h2 hm) hQ''
  have hQ₁''nd : Q₁''.Nondegenerate := nondegenerate_compMat v hQ'' hP''
  have hQ₁nd : (splitForm m Q₁'').Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]; exact mul_ne_zero (mul_ne_zero h2 hm) hQ₁''nd
  -- exponents
  obtain ⟨c, hc⟩ := dvd_pow_ord v hP''
  have hcP : P.det ∣ NF.π v ^ c := by rw [hdetP]; exact hc
  obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h2 hm)
  have h4 : (4 * m : 𝔬) ≠ 0 := by
    rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero h2 h2) hm
  obtain ⟨f, hf, hf'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ h4
  obtain ⟨d₁, hd₁, hd₁'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hQ₁nd
  obtain ⟨d₂, hd₂, hd₂'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hQo
  set r := f + 1 + c
  -- the densities at a common large level
  have ev := (localDensityForm_self_eventually_eq Qo hQo (NF.π v) hπ).and
    ((localDensityForm_self_eventually_eq (splitForm m Q₁'') hQ₁nd (NF.π v) hπ).and
      ((localDensityForm_self_eventually_eq Q'' hQ'' (NF.π v) hπ).and
        ((localDensityForm_self_eventually_eq Q₁'' hQ₁''nd (NF.π v) hπ).and
          (Filter.eventually_ge_atTop (r + c + e + 2 * e + 1 + r + d₁ + 2 * d₁ + d₂ + 2 * d₂ + c + 1)))))
  obtain ⟨k, hβ₂, hβ₁, hβ₂'', hβ₁'', hk⟩ := ev.exists
  -- REL
  set Qv := Qo.map (algebraMap 𝔬 Fv)
  set h := glOf v P hP
  have hy : (Qo.compMat P).eval (e₀ : Fin (n + 1) → 𝔬) = m := by rw [hQ₁, eval_splitForm_e₀']
  have hPe : P *ᵥ (e₀ : Fin (n + 1) → 𝔬) = e₀ := by
    rw [show P = cornerMat 1 P'' from rfl, show (e₀ : Fin (n + 1) → 𝔬) = Fin.cons 1 0 from rfl,
      cornerMat_mulVec, one_mul, mulVec_zero]
  have hrel := rel_local v Qo hQo P hP hcP hm he he' hf hf' e₀ hy (k := k) (r := r) le_rfl (by omega) (by omega)
  rw [hPe] at hrel
  -- the orbits of `e₀`
  have hQ₁v : (splitForm m Q₁'').map (algebraMap 𝔬 Fv) = Qv.compMat h.val := by
    rw [← hQ₁]; exact integralModel_compMat v rfl P hP
  have hρ₁Q : ∀ κ, (splitForm m Q₁'').compMat (repAt v Qv h κ) = splitForm m Q₁'' :=
    compMat_repAt v h hQ₁v
  have hsurj₁ : ∀ X, (splitForm m Q₁'').compMat X = splitForm m Q₁'' → ∃ κ, repAt v Qv h κ = X :=
    exists_repAt_eq v h hQ₁v hQ₁nd
  have horb₁ := card_orbitSet_eq_nearCount (n := n) hπ (repAt v Qv h) Q₁'' hρ₁Q hsurj₁ hf hf' hd₁ hd₁'
    (r := r) (k := k) (by omega) (by omega) (by omega)
  have horb₂ := card_orbitSet_eq_nearCount (n := n) hπ (repStd v Qv) Q'' (compMat_repStd v rfl)
    (exists_repStd_eq v rfl hQo) hf hf' hd₂ hd₂' (r := r) (k := k) (by omega) (by omega) (by omega)
  have hW₁ := repCountForm_splitForm_orbit (k := k) hπ he he' Q₁'' hd₁ hd₁' (by omega) (by omega)
  have hW₂ := repCountForm_splitForm_orbit (k := k) hπ he he' Q'' hd₂ hd₂' (by omega) (by omega)
  rw [hQ₁] at hrel
  rw [← horb₁, ← horb₂] at hrel
  -- the stabilizers of `e₀`
  set Q''v := Q''.map (algebraMap 𝔬 Fv)
  set h'' := glOf v P'' hP''
  have hh : h = blockGL h'' := glOf_cornerMat v P'' hP'' hP
  have hQv : Qv = splitForm (algebraMap 𝔬 Fv m) Q''v := map_splitForm _ _ _
  have hm' : algebraMap 𝔬 Fv m ≠ 0 := fun h0 => hm (Subtype.ext (by simpa using h0))
  set K₁ := KL v Qv (locAct v h (std v))
  set K₂ := KL v Qv (std v)
  set K₁'' := KL v Q''v (locAct v h'' (std v))
  set K₂'' := KL v Q''v (std v)
  have hstd : (std v : Submodule 𝔬 (Fin (n + 1) → Fv)) = locAct v (blockGL 1) (std v) := by
    rw [map_one, locAct_one]
  have hstd'' : (std v : Submodule 𝔬 (Fin n → Fv)) = locAct v 1 (std v) := by rw [locAct_one]
  have hS₁ := stab_e₀_map' v hm' hQv (Λ := locAct v h (std v)) (h'' := h'') (by rw [hh]) (repAt v Qv h)
    (repAt_mulVec_e₀_iff v h (by rw [hh]; exact blockGL_mulVec_e₀ h''))
  have hS₂ := stab_e₀_map' v hm' hQv (Λ := std v) (h'' := 1) hstd (repStd v Qv) (repStd_mulVec_e₀_iff v)
  have hmem2 : ∀ g ∈ K₁'', blockGL g ∈ K₂ ↔ g ∈ K₂'' := by
    intro g _
    show blockGL g ∈ KL v Qv (std v) ↔ g ∈ KL v Q''v (std v)
    rw [hQv, hstd, blockGL_mem_KL_iff v _ Q''v g 1, ← hstd'']
  have hmem1 : ∀ g ∈ K₂'', blockGL g ∈ K₁ ↔ g ∈ K₁'' := by
    intro g _
    show blockGL g ∈ KL v Qv (locAct v h (std v)) ↔ g ∈ KL v Q''v (locAct v h'' (std v))
    rw [hQv, hh, blockGL_mem_KL_iff v _ Q''v g h'']
  rw [← hstd''] at hS₂
  have hs₁ := relIndex_stab_eq K₁ K₂ _ blockGL K₁'' K₂'' hS₁ hmem2
  have hs₂ := relIndex_stab_eq K₂ K₁ _ blockGL K₂'' K₁'' hS₂ hmem1
  rw [hs₁, hs₂] at hrel
  -- the index
  have hind := card_ker_redMat_eq v P hP (k := k) ((hcP).trans (pow_dvd_pow _ (by omega)))
  -- positivity
  have hlat₁ : (locAct v h (std v)).IsLattice Fv := locAct_isLattice _ (std_isLattice v)
  have hcom := commens_KL v Qv hlat₁ (std_isLattice v)
  have hcom'' := commens_KL v Q''v (locAct_isLattice h'' (std_isLattice v)) (std_isLattice v)
  set a := K₂.relIndex K₁
  set b := K₁.relIndex K₂
  set s₁ := K₂''.relIndex K₁''
  set s₂ := K₁''.relIndex K₂''
  have hb : (0 : ℝ) < b := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcom.2)
  have hs₂0 : (0 : ℝ) < s₂ := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcom''.2)
  have hq : (0 : ℝ) < q 𝔬 := Nat.cast_pos.mpr q_pos
  have hD : (0 : ℝ) < ‖((P''.det : 𝔬) : Fv)‖ := norm_pos_iff.mpr (fun h0 => hP'' (Subtype.ext (by simpa using h0)))
  -- unfold the goal and the hypothesis
  unfold AlphaLawAt at ih ⊢
  rw [hQ₁, hdetP]
  have hr1 : relRatio K₁ K₂ = (a : ℝ) / b := rfl
  have hr2 : relRatio K₁'' K₂'' = (s₁ : ℝ) / s₂ := rfl
  rw [show KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v)) = K₁ from rfl,
    show KL v (Qo.map (algebraMap 𝔬 Fv)) (std v) = K₂ from rfl, hr1]
  rw [show KL v (Q''.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P'' hP'') (std v)) = K₁'' from rfl,
    show KL v (Q''.map (algebraMap 𝔬 Fv)) (std v) = K₂'' from rfl, hr2] at ih
  rw [← hβ₂, ← hβ₁]
  rw [← hβ₂'', ← hβ₁''] at ih
  rw [hW₁, hW₂]
  set D := ‖((P''.det : 𝔬) : Fv)‖
  set O₁ := Nat.card (orbitSet ((splitForm m Q₁'').map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k}))) e₀)
  set O₂ := Nat.card (orbitSet ((splitForm m Q'').map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k}))) e₀)
  set A₁ := repCountForm Q₁'' Q₁'' (NF.π v) k
  set A₂ := repCountForm Q'' Q'' (NF.π v) k
  have hR : (O₁ : ℝ) * s₁ * b = (Nat.card (redMat (NF.π v) k P).ker : ℝ) * a * O₂ * s₂ := by exact_mod_cast hrel
  rw [hind, hdetP] at hR
  have hO₂ : (0 : ℝ) < O₂ := by
    have hpos : 0 < repCountForm (splitForm m Q'') (splitForm m Q'') (NF.π v) k := by
      have := finite_quot_pow (NF.π v) hπ k
      unfold repCountForm
      exact Nat.card_pos_iff.mpr ⟨⟨⟨1, by rw [compMat_one]⟩⟩, inferInstance⟩
    rw [hW₂] at hpos
    exact_mod_cast Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right hpos)
  have hA₂ : (0 : ℝ) < A₂ := by
    have hpos : 0 < repCountForm Q'' Q'' (NF.π v) k := by
      have := finite_quot_pow (NF.π v) hπ k
      unfold repCountForm
      exact Nat.card_pos_iff.mpr ⟨⟨⟨1, by rw [compMat_one]⟩⟩, inferInstance⟩
    exact_mod_cast hpos
  have hZ : (0 : ℝ) < (q 𝔬 : ℝ) ^ (k * ((n + 1) * (n + 1 - 1) / 2)) := pow_pos hq _
  have hZ'' : (0 : ℝ) < (q 𝔬 : ℝ) ^ (k * (n * (n - 1) / 2)) := pow_pos hq _
  push_cast at ih ⊢
  generalize (q 𝔬 : ℝ) ^ (k * ((n + 1) * (n + 1 - 1) / 2)) = Z at hZ ⊢
  generalize (q 𝔬 : ℝ) ^ (k * (n * (n - 1) / 2)) = Z'' at hZ'' ih
  generalize (q 𝔬 : ℝ) ^ (e * n) = W
  -- from the induction hypothesis: `s₁ A₂ = s₂ A₁ D^(n+1)`
  have ih' : (s₁ : ℝ) * A₂ = s₂ * A₁ * D ^ (n + 1) := by
    field_simp at ih
    linear_combination ih
  -- from REL: `O₁ s₁ b D = a O₂ s₂`
  have hR' : (O₁ : ℝ) * s₁ * b * D = a * O₂ * s₂ := by
    rw [hR, show ‖((P''.det : 𝔬) : Fv)‖⁻¹ = D⁻¹ from rfl]; field_simp
  have key : (a : ℝ) * O₂ * A₂ * s₂ = b * O₁ * A₁ * D ^ (n + 1 + 1) * s₂ := by
    linear_combination (A₂ : ℝ) * hR'.symm + (O₁ : ℝ) * b * D * ih'
  have key' : (a : ℝ) * O₂ * A₂ = b * O₁ * A₁ * D ^ (n + 1 + 1) := mul_right_cancel₀ hs₂0.ne' key
  field_simp
  linear_combination W * key'

end SplitStep

end QuadFormsKB.Tamagawa
