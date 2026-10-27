/-
# The local orbital identity at the non-standard primes

**Layer:** the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ at a finite prime (every residue characteristic), then the frames of
The orbital Euler product.

`OrbitalEuler` proved `OrbitalLocalIdentityAt` at the *standard* primes of a frame ($g^{-1}L_\mathfrak p = \mathfrak o_\mathfrak p^{n+1}$, $0 \le \mathrm{ord}\,\rho \le 1$)
and left the others as the input `OrbitalLocalIdentities`. Here the identity is proved at **every** prime where the $\alpha$
transformation law holds (`AlphaLawAt`), in particular at every $\mathfrak p \nmid 2$ (`alphaLaw_odd`).

**The per-vector identity** (`perY`). Let $\Lambda = \mathfrak o_\mathfrak p^{N}$ carry the integral form $Q_o$ ($N = n+1$) and let
$\Lambda_1 = P\,\mathfrak o_\mathfrak p^N \subseteq \Lambda$ be a sublattice in which $y = Pe_0$ splits: $Q_o\circ P = \langle t\rangle\perp Q''$. Then
$$r\big(\mathrm{St}_{K(\Lambda_1)}(y), \mathrm{St}_{K(\Lambda)}(y)\big)\,\beta(Q_o)\,q^{kn} = N_{k,r}\big(K(\Lambda)y\big)\,\|\det P\|^{n+1}\,q^{en}\,\beta(Q''),$$
$\varpi^e\,\Vert\,2t$: REL (`rel_local`) at $y$ and the $\alpha$ law for $\Lambda_1 \subseteq \Lambda$ turn the index ratio into the ratio of the near
counts of the two orbits of $y$, and the orbit count in the split case gives the orbit of $y = e_0$ in the split lattice $\Lambda_1$.

Sources: Weil 1982, §3.4 and §4.5, p. 109 [unverified]; Hanke 2004, §3, Def. 3.1 and the maps $\pi_Z$, $\pi_{B'}$, $\pi_{B''}$, pp. 358–361. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.AlphaLawOdd

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices QuadForm LocalDensity LocalDensity.DVR

/-! ### Stabilizers of a vector -/

section StabV

variable {G : Type*} [Group G]

/-- If $S \le K_1$ maps onto $K_1 \cap T$, then $[S : S \cap K_2] = [K_1\cap T : K_1\cap K_2\cap T]$. -/
theorem relIndex_subgroupOf_eq (K₁ K₂ T : Subgroup G) (S : Subgroup K₁) (hS : S.map K₁.subtype = K₁ ⊓ T) :
    (K₂.subgroupOf K₁).relIndex S = (K₂ ⊓ T).relIndex (K₁ ⊓ T) := by
  rw [← Subgroup.relIndex_map_map_of_injective _ _ K₁.subtype_injective, Subgroup.subgroupOf_map_subtype, hS,
    ← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right (K₂ ⊓ T)]
  congr 1
  ext g
  simp only [Subgroup.mem_inf]
  tauto

theorem relIndex_inf_inf_ne_zero {K₁ K₂ : Subgroup G} (T : Subgroup G) (h : K₁.relIndex K₂ ≠ 0) :
    (K₁ ⊓ T).relIndex (K₂ ⊓ T) ≠ 0 := by
  have e : (K₁ ⊓ T).relIndex (K₂ ⊓ T) = K₁.relIndex (K₂ ⊓ T) := by
    rw [← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right K₁]
    congr 1; ext; simp only [Subgroup.mem_inf]; tauto
  rw [e]
  exact fun h0 => h (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h0)

theorem commens_inf {K₁ K₂ : Subgroup G} (T : Subgroup G) (h : Commens K₁ K₂) : Commens (K₁ ⊓ T) (K₂ ⊓ T) :=
  ⟨relIndex_inf_inf_ne_zero T h.1, relIndex_inf_inf_ne_zero T h.2⟩

end StabV

section StabVLocal

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The stabilizer of a vector** $w \in F_\mathfrak p^N$ in $\mathrm{GL}_N(F_\mathfrak p)$. -/
def stabV (w : Fin N → Fv) : Subgroup (GL (Fin N) Fv) where
  carrier := {g | g.val *ᵥ w = w}
  mul_mem' {a b} ha hb := by
    show (a * b).val *ᵥ w = w
    rw [Units.val_mul, ← mulVec_mulVec, show b.val *ᵥ w = w from hb, show a.val *ᵥ w = w from ha]
  one_mem' := by show (1 : GL (Fin N) Fv).val *ᵥ w = w; simp
  inv_mem' {a} ha := by
    show a⁻¹.val *ᵥ w = w
    conv_lhs => rw [← show a.val *ᵥ w = w from ha]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem mem_stabV {w : Fin N → Fv} {g : GL (Fin N) Fv} : g ∈ stabV v w ↔ g.val *ᵥ w = w := Iff.rfl

theorem stabV_map_conj (h : GL (Fin N) Fv) (w : Fin N → Fv) :
    (stabV v w).map (MulAut.conj h).toMonoidHom = stabV v (h.val *ᵥ w) := by
  ext g
  rw [Subgroup.mem_map_equiv (f := MulAut.conj h), MulAut.conj_symm_apply, mem_stabV, mem_stabV]
  constructor
  · intro hg
    have := congrArg (h.val *ᵥ ·) hg
    simp only [Units.val_mul, ← mulVec_mulVec] at this
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this
  · intro hg
    simp only [Units.val_mul, ← mulVec_mulVec, hg]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem stabOf_repAt_map (Qv : QuadForm Fv N) (h : GL (Fin N) Fv) (u : Fin N → 𝔬) :
    (stabOf (repAt v Qv h) u).map (KL v Qv (locAct v h (std v))).subtype =
      KL v Qv (locAct v h (std v)) ⊓ stabV v (h.val *ᵥ fun i => (u i : Fv)) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_stabV]
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    refine ⟨κ.2, ?_⟩
    have h1 : (repAt v Qv h κ *ᵥ u) = u := hκ
    have h2 := congrArg (fun z : Fin N → 𝔬 => fun i => (z i : Fv)) h1
    rw [coe_mulVec_o, repAt_map] at h2
    have := congrArg (h.val *ᵥ ·) h2
    simp only [Units.val_mul, ← mulVec_mulVec] at this
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this
  · rintro ⟨hg, hgw⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show repAt v Qv h ⟨g, hg⟩ *ᵥ u = u
    apply coe_o_injective v
    show (fun i => ((repAt v Qv h ⟨g, hg⟩ *ᵥ u) i : Fv)) = fun i => (u i : Fv)
    rw [coe_mulVec_o, repAt_map]
    simp only [Units.val_mul, ← mulVec_mulVec, hgw]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem stabOf_repStd_map (Qv : QuadForm Fv N) (u : Fin N → 𝔬) :
    (stabOf (repStd v Qv) u).map (KL v Qv (std v)).subtype =
      KL v Qv (std v) ⊓ stabV v (fun i => (u i : Fv)) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_stabV]
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    refine ⟨κ.2, ?_⟩
    have h1 : (repStd v Qv κ *ᵥ u) = u := hκ
    have h2 := congrArg (fun z : Fin N → 𝔬 => fun i => (z i : Fv)) h1
    rwa [coe_mulVec_o, repStd_map] at h2
  · rintro ⟨hg, hgw⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show repStd v Qv ⟨g, hg⟩ *ᵥ u = u
    apply coe_o_injective v
    show (fun i => ((repStd v Qv ⟨g, hg⟩ *ᵥ u) i : Fv)) = fun i => (u i : Fv)
    rw [coe_mulVec_o, repStd_map]
    exact hgw

end StabVLocal

/-! ### The per-vector identity -/

section PerY

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The per-vector identity** (Weil 1982, §3.4 [unverified]; every prime where the $\alpha$ law holds). For $Q_o$ over $\mathfrak o_\mathfrak p$
in $n + 1$ variables and an integral $P$ with $Q_o\circ P = \langle t\rangle\perp Q''$ ($t \ne 0$; so $y = Pe_0$ splits the sublattice
$\Lambda_1 = P\mathfrak o_\mathfrak p^{n+1}$), with $K_1 = K(\Lambda_1)$, $K_2 = K(\mathfrak o_\mathfrak p^{n+1})$: for all large $r$ and $k$,
$$r\big(\mathrm{St}_{K_1}(y), \mathrm{St}_{K_2}(y)\big)\,\beta(Q_o)\,q^{kn} = N_{k,r}(K_2y)\,\|\det P\|^{n+1}\,q^{en}\,\beta(Q''),\qquad \varpi^e\,\Vert\,2t.$$ -/
theorem perY (Qo : QuadForm 𝔬 (n + 1)) (hQo : Qo.Nondegenerate) (Q'' : QuadForm 𝔬 n) (hQ'' : Q''.Nondegenerate)
    {t : 𝔬} (ht : t ≠ 0) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬) (hP : P.det ≠ 0)
    (hsplit : Qo.compMat P = splitForm t Q'') (hlaw : AlphaLawAt v Qo P hP) {e : ℕ}
    (he : NF.π v ^ e ∣ 2 * t) (he' : ¬ NF.π v ^ (e + 1) ∣ 2 * t) :
    ∃ r₀ : ℕ, ∀ r, r₀ ≤ r → ∀ᶠ k in Filter.atTop,
      relRatio (KL v (Qo.map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v)) ⊓
          stabV v ((glOf v P hP).val *ᵥ (e₀ : Fin (n + 1) → Fv)))
        (KL v (Qo.map (algebraMap 𝔬 Fv)) (std v) ⊓ stabV v ((glOf v P hP).val *ᵥ (e₀ : Fin (n + 1) → Fv))) *
          localDensityForm Qo Qo (NF.π v) * (q 𝔬 : ℝ) ^ (k * n) =
        nearCount Qo (NF.π v) t k r (orbitOf (repStd v (Qo.map (algebraMap 𝔬 Fv))) ⊤ (P *ᵥ e₀)) *
          ‖((P.det : 𝔬) : Fv)‖ ^ (n + 1) * (q 𝔬 : ℝ) ^ (e * n) * localDensityForm Q'' Q'' (NF.π v) := by
  classical
  have hπ := NF.irreducible_π v
  have h2 := NF.two_ne_zero' v
  set Qv := Qo.map (algebraMap 𝔬 Fv)
  set h := glOf v P hP
  set K₁ := KL v Qv (locAct v h (std v))
  set K₂ := KL v Qv (std v)
  set yv := h.val *ᵥ (e₀ : Fin (n + 1) → Fv)
  have hyv : yv = fun i => (((P *ᵥ e₀) i : 𝔬) : Fv) := by
    rw [coe_mulVec_o, coe_e₀_o']; rfl
  obtain ⟨c, hc⟩ := dvd_pow_ord v hP
  have h4 : (4 * t : 𝔬) ≠ 0 := by
    rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero h2 h2) ht
  obtain ⟨f, hf, hf'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ h4
  have hsnd : (splitForm t Q'').Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]; exact mul_ne_zero (mul_ne_zero h2 ht) hQ''
  obtain ⟨d₁, hd₁, hd₁'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hsnd
  refine ⟨f + 1 + c, fun r hr => ?_⟩
  filter_upwards [localDensityForm_self_eventually_eq Qo hQo (NF.π v) hπ,
    localDensityForm_self_eventually_eq (splitForm t Q'') hsnd (NF.π v) hπ,
    localDensityForm_self_eventually_eq Q'' hQ'' (NF.π v) hπ,
    Filter.eventually_ge_atTop (r + c + e + 2 * e + 1 + r + d₁ + 2 * d₁ + c + 1)] with k hβ hβs hβ'' hk
  -- REL at `e₀`
  have hy : (Qo.compMat P).eval (e₀ : Fin (n + 1) → 𝔬) = t := by rw [hsplit, eval_splitForm_e₀']
  have hrel := rel_local v Qo hQo P hP hc ht he he' hf hf' e₀ hy (k := k) (r := r) hr (by omega) (by omega)
  -- the stabilizers
  have hs₁ : (K₂.subgroupOf K₁).relIndex (stabOf (repAt v Qv h) e₀) = (K₂ ⊓ stabV v yv).relIndex (K₁ ⊓ stabV v yv) :=
    relIndex_subgroupOf_eq K₁ K₂ _ _ (by rw [stabOf_repAt_map, coe_e₀_o'])
  have hs₂ : (K₁.subgroupOf K₂).relIndex (stabOf (repStd v Qv) (P *ᵥ e₀)) =
      (K₁ ⊓ stabV v yv).relIndex (K₂ ⊓ stabV v yv) :=
    relIndex_subgroupOf_eq K₂ K₁ _ _ (by rw [stabOf_repStd_map, ← hyv])
  rw [hs₁, hs₂] at hrel
  -- the orbit of `e₀` in the split lattice
  have hQ₁v : (splitForm t Q'').map (algebraMap 𝔬 Fv) = Qv.compMat h.val := by
    rw [← hsplit]; exact integralModel_compMat v rfl P hP
  have horb := card_orbitSet_eq_nearCount (n := n) hπ (repAt v Qv h) Q''
    (compMat_repAt v h hQ₁v) (exists_repAt_eq v h hQ₁v hsnd) hf hf' hd₁ hd₁' (r := r) (k := k)
    (by omega) (by omega) (by omega)
  have hW := repCountForm_splitForm_orbit (k := k) hπ he he' Q'' hd₁ hd₁' (by omega) (by omega)
  rw [hsplit, ← horb] at hrel
  have hind := card_ker_redMat_eq v P hP (k := k) (hc.trans (pow_dvd_pow _ (by omega)))
  -- positivity
  have hlat : (locAct v h (std v)).IsLattice Fv := locAct_isLattice _ (std_isLattice v)
  have hcom := commens_KL v Qv hlat (std_isLattice v)
  have hb : (0 : ℝ) < K₁.relIndex K₂ := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcom.2)
  have hcomS : Commens (K₁ ⊓ stabV v yv) (K₂ ⊓ stabV v yv) := commens_inf _ hcom
  have hs2 : (0 : ℝ) < (K₁ ⊓ stabV v yv).relIndex (K₂ ⊓ stabV v yv) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcomS.2)
  have hq : (0 : ℝ) < q 𝔬 := Nat.cast_pos.mpr q_pos
  have hA'' : (0 : ℝ) < repCountForm Q'' Q'' (NF.π v) k := by
    have := finite_quot_pow (NF.π v) hπ k
    have : 0 < repCountForm Q'' Q'' (NF.π v) k := by
      unfold repCountForm
      exact Nat.card_pos_iff.mpr ⟨⟨⟨1, by rw [compMat_one]⟩⟩, inferInstance⟩
    exact_mod_cast this
  have hO₁ : (0 : ℝ) < Nat.card (orbitSet ((splitForm t Q'').map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k}))) e₀) := by
    have hpos : 0 < repCountForm (splitForm t Q'') (splitForm t Q'') (NF.π v) k := by
      have := finite_quot_pow (NF.π v) hπ k
      unfold repCountForm
      exact Nat.card_pos_iff.mpr ⟨⟨⟨1, by rw [compMat_one]⟩⟩, inferInstance⟩
    rw [hW] at hpos
    exact_mod_cast Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right hpos)
  -- the law
  unfold AlphaLawAt at hlaw
  rw [hsplit, ← hβs] at hlaw
  rw [← hβ'']
  set a := K₂.relIndex K₁
  set b := K₁.relIndex K₂
  set s₁ := (K₂ ⊓ stabV v yv).relIndex (K₁ ⊓ stabV v yv)
  set s₂ := (K₁ ⊓ stabV v yv).relIndex (K₂ ⊓ stabV v yv)
  set O₁ := Nat.card (orbitSet ((splitForm t Q'').map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k}))) e₀)
  set N₂ := nearCount Qo (NF.π v) t k r (orbitOf (repStd v Qv) ⊤ (P *ᵥ e₀))
  set D := ‖((P.det : 𝔬) : Fv)‖
  have hR : (O₁ : ℝ) * s₁ * b = (Nat.card (redMat (NF.π v) k P).ker : ℝ) * a * N₂ * s₂ := by exact_mod_cast hrel
  rw [hind] at hR
  have hW' : (repCountForm (splitForm t Q'') (splitForm t Q'') (NF.π v) k : ℝ) =
      O₁ * (q 𝔬 : ℝ) ^ (e * n) * repCountForm Q'' Q'' (NF.π v) k := by exact_mod_cast hW
  rw [hW'] at hlaw
  have hD : 0 < D := norm_pos_iff.mpr (fun h0 => hP (Subtype.ext (by simpa using h0)))
  have hr1 : relRatio (K₁ ⊓ stabV v yv) (K₂ ⊓ stabV v yv) = (s₁ : ℝ) / s₂ := rfl
  have hr2 : relRatio K₁ K₂ = (a : ℝ) / b := rfl
  rw [hr1]
  rw [hr2] at hlaw
  set B := localDensityForm Qo Qo (NF.π v)
  set A'' := (repCountForm Q'' Q'' (NF.π v) k : ℝ)
  have hE : (k * ((n + 1) * (n + 1 - 1) / 2)) = k * (n * (n - 1) / 2) + k * n := by
    rw [← mul_add]; congr 1
    have h3 : (n + 1) * (n + 1 - 1) = n * (n - 1) + 2 * n := by
      rcases n with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]; ring
    rw [h3, Nat.add_mul_div_left _ _ two_pos]
  rw [hE, pow_add] at hlaw
  have hZ : (0 : ℝ) < (q 𝔬 : ℝ) ^ (k * (n * (n - 1) / 2)) := pow_pos hq _
  have hZn : (0 : ℝ) < (q 𝔬 : ℝ) ^ (k * n) := pow_pos hq _
  generalize (q 𝔬 : ℝ) ^ (k * (n * (n - 1) / 2)) = Z at hZ hlaw ⊢
  generalize (q 𝔬 : ℝ) ^ (k * n) = Zn at hZn hlaw ⊢
  generalize (q 𝔬 : ℝ) ^ (e * n) = W at hlaw ⊢
  have hR' : (O₁ : ℝ) * s₁ * b * D = N₂ * s₂ * a := by rw [hR]; field_simp
  field_simp at hlaw
  rw [show (s₁ : ℝ) / s₂ * B * Zn = s₁ * B * Zn / s₂ by ring,
    show (N₂ : ℝ) * D ^ (n + 1) * W * (A'' / Z) = N₂ * D ^ (n + 1) * W * A'' / Z by ring,
    div_eq_div_iff hs2.ne' hZ.ne']
  have hO₁bD : (O₁ : ℝ) * b * D ≠ 0 := by positivity
  refine mul_left_cancel₀ hO₁bD ?_
  linear_combination (B * Zn * Z) * hR' + (N₂ * s₂ : ℝ) * hlaw

end PerY

/-! ### The weights of the local types as index ratios in $\mathrm{GL}_{n+1}(F_\mathfrak p)$ -/

section FrameGroups

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem mem_orthGroup_iff_compMat {N : ℕ} (Q : QuadForm F N) (g : GL (Fin N) Fv) :
    g ∈ orthGroup Q Fv ↔ (Q.map (algebraMap F Fv)).compMat g.val = Q.map (algebraMap F Fv) := by
  constructor
  · intro hg
    refine eq_of_eval_eq fun z => ?_
    rw [eval_compMat, ← evalIn_eq_eval_map, ← evalIn_eq_eval_map, evalIn_mulVec_of_mem Q hg]
  · intro h
    refine mem_orthGroup_of_evalIn Q fun z => ?_
    rw [evalIn_eq_eval_map, evalIn_eq_eval_map, ← eval_compMat, h]

variable (m : F) (Q' : QuadForm F n)

/-- $O(Q') \to \mathrm{GL}_{n+1}(F_\mathfrak p)$, $a \mapsto \mathrm{diag}(1, a)$. -/
def embO : orthGroup Q' Fv →* GL (Fin (n + 1)) Fv :=
  (orthGroup (splitForm m Q') Fv).subtype.comp (orthEmb m Q' Fv)

theorem embO_injective : Function.Injective (embO v m Q') :=
  (orthGroup (splitForm m Q') Fv).subtype_injective.comp (orthEmb_injective m Q' Fv)

theorem embO_apply (a : orthGroup Q' Fv) : embO v m Q' a = blockGL (a : GL (Fin n) Fv) := rfl

theorem stabV_smul_e₀ {c : Fv} (hc : c ≠ 0) (g : GL (Fin (n + 1)) Fv) :
    g ∈ stabV v (c • (e₀ : Fin (n + 1) → Fv)) ↔ g.val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
  rw [mem_stabV, mulVec_smul]
  exact ⟨fun h => smul_right_injective _ hc h, fun h => by rw [h]⟩

theorem exists_embO_eq (hm : m ≠ 0) {c : Fv} (hc : c ≠ 0) {g : GL (Fin (n + 1)) Fv}
    (hg : ((splitForm m Q').map (algebraMap F Fv)).compMat g.val = (splitForm m Q').map (algebraMap F Fv))
    (hge : g ∈ stabV v (c • (e₀ : Fin (n + 1) → Fv))) : ∃ a, embO v m Q' a = g := by
  have hm2 : algebraMap F Fv (2 * m) ≠ 0 := by rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm
  have hgO : g ∈ orthGroup (splitForm m Q') Fv := (mem_orthGroup_iff_compMat v _ g).mpr hg
  obtain ⟨a, ha⟩ := exists_orthEmb_eq m Q' Fv hm2 ⟨g, hgO⟩ ((stabV_smul_e₀ v hc g).mp hge)
  exact ⟨a, by rw [embO, MonoidHom.comp_apply, ha]; rfl⟩

/-- **The stabilizer of a local type** maps onto $K(M)\cap\mathrm{St}(c\,e_0)$. -/
theorem map_stabilizer_eq (hm : m ≠ 0) {Λ : Submodule 𝔬 (Fin (n + 1) → Fv)} {c : Fv} (hc : c ≠ 0)
    (M : LocCompSetG v m Q' Λ c) :
    (stabilizer (orthGroup Q' Fv) M).map (embO v m Q') =
      KL v ((splitForm m Q').map (algebraMap F Fv)) M.1 ⊓ stabV v (c • (e₀ : Fin (n + 1) → Fv)) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_KL]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨(mem_orthGroup_iff_compMat v _ _).mp (orthEmb m Q' Fv a).2, congrArg Subtype.val ha⟩, ?_⟩
    rw [stabV_smul_e₀ v hc]; exact blockGL_mulVec_e₀ _
  · rintro ⟨⟨hgQ, hgM⟩, hge⟩
    obtain ⟨a, rfl⟩ := exists_embO_eq v m Q' hm hc hgQ hge
    exact ⟨a, Subtype.ext hgM, rfl⟩

/-- $D = \mathrm{diag}(c, \varpi^b, \dots, \varpi^b)$. -/
def dMat {c : Fv} (hc : c ≠ 0) (b : ℕ) : GL (Fin (n + 1)) Fv :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (cornerMat c (((NF.π v : 𝔬) : Fv) ^ b • (1 : Matrix (Fin n) (Fin n) Fv)))
    (by
      rw [det_cornerMat, det_smul, det_one, mul_one]
      exact mul_ne_zero hc (pow_ne_zero _ (pow_ne_zero _ (fun h => (NF.irreducible_π v).ne_zero
        (Subtype.ext (by simpa using h))))))

theorem dMat_val {c : Fv} (hc : c ≠ 0) (b : ℕ) :
    (dMat v hc b : GL (Fin (n + 1)) Fv).val =
      cornerMat c (((NF.π v : 𝔬) : Fv) ^ b • (1 : Matrix (Fin n) (Fin n) Fv)) := rfl

theorem dMat_comm {c : Fv} (hc : c ≠ 0) (b : ℕ) (a : GL (Fin n) Fv) :
    dMat v hc b * blockGL a = blockGL a * dMat v hc b := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dMat_val, blockGL_val, cornerMat_mul, cornerMat_mul, mul_one, one_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- **The reference stabilizer** $\mathrm{diag}(1, O(\mathfrak o_\mathfrak p^n))$ is $K(D\,\mathfrak o_\mathfrak p^{n+1})\cap\mathrm{St}(c\,e_0)$. -/
theorem map_stdStab_eq (hm : m ≠ 0) {c : Fv} (hc : c ≠ 0) (b : ℕ) :
    (stdStab Q' v).map (embO v m Q') =
      KL v ((splitForm m Q').map (algebraMap F Fv)) (locAct v (dMat v hc b) (std v)) ⊓
        stabV v (c • (e₀ : Fin (n + 1) → Fv)) := by
  have key : ∀ a : GL (Fin n) Fv, locAct v (blockGL a) (locAct v (dMat v hc b) (std v)) =
      locAct v (dMat v hc b) (std v) ↔ locAct v a (std v) = std v := by
    intro a
    rw [← locAct_mul, ← dMat_comm, locAct_mul, ← locAct_blockGL_std_iff]
    constructor
    · intro h
      have := congrArg (locAct v (dMat v hc b)⁻¹) h
      rwa [locAct_inv_locAct, locAct_inv_locAct] at this
    · intro h; rw [h]
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_KL]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨(mem_orthGroup_iff_compMat v _ _).mp (orthEmb m Q' Fv a).2, ?_⟩, ?_⟩
    · rw [embO_apply, key]; exact ha
    · rw [stabV_smul_e₀ v hc]; exact blockGL_mulVec_e₀ _
  · rintro ⟨⟨hgQ, hgD⟩, hge⟩
    obtain ⟨a, rfl⟩ := exists_embO_eq v m Q' hm hc hgQ hge
    refine ⟨a, ?_, rfl⟩
    rw [embO_apply, key] at hgD
    exact hgD

end FrameGroups

/-! ### The frame in local coordinates -/

section FrameData

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem map_Qp_eq {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) :
    (NF.Qp v Q₀).map (algebraMap 𝔬 Fv) = (Q₀.map (algebraMap (𝓞 F) F)).map (algebraMap F Fv) := by
  rw [QuadForm.map_map, QuadForm.map_map]; congr 1

theorem splitForm_compMat_corner {A : Type*} [CommRing A] (a c : A) (Q' : QuadForm A n) (X : Matrix (Fin n) (Fin n) A) :
    (splitForm a Q').compMat (cornerMat c X) = splitForm (c ^ 2 * a) (Q'.compMat X) := by
  refine eq_of_eval_eq fun x => ?_
  rw [eval_compMat, ← Fin.cons_self_tail x, cornerMat_mulVec, eval_splitForm_cons, eval_splitForm_cons, eval_compMat]
  ring

theorem compMat_smul_one {A : Type*} [CommRing A] (Q' : QuadForm A n) (d : A) :
    Q'.compMat (d • (1 : Matrix (Fin n) (Fin n) A)) = (d ^ 2) • Q' := by
  refine eq_of_eval_eq fun x => ?_
  rw [eval_compMat, smul_mulVec, one_mulVec, eval_smul_gen, eval_smul_form_gen]

/-- **The frame over $F_\mathfrak p$**: $Q_0\circ g = \langle\rho\rangle\perp Q'$ with the integral model of $Q_0$. -/
theorem frame_local {Q₀ : QuadForm (𝓞 F) (n + 1)} {ρ : F} (fr : AdaptedFrame (HilbertModular.formF Q₀) ρ) :
    ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)).compMat (Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g).val =
      (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))).map (algebraMap F Fv) := by
  rw [map_Qp_eq, ← fr.compMat_eq, ← map_compMat]
  rfl

theorem frameLat_eq {Q : QuadForm F (n + 1)} {ρ : F} (fr : AdaptedFrame Q ρ) :
    frameLat v fr.g = locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g)⁻¹ (std v) := by
  rw [frameLat, loc_glImage, loc_intVec, map_inv]

theorem mul_cornerMat_apply_zero (X : Matrix (Fin (n + 1)) (Fin (n + 1)) Fv) (c d : Fv) (i : Fin (n + 1)) :
    (X * cornerMat c (d • (1 : Matrix (Fin n) (Fin n) Fv))) i 0 = X i 0 * c := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [cornerMat]

theorem mul_cornerMat_apply_succ (X : Matrix (Fin (n + 1)) (Fin (n + 1)) Fv) (c d : Fv) (i : Fin (n + 1))
    (k : Fin n) : (X * cornerMat c (d • (1 : Matrix (Fin n) (Fin n) Fv))) i k.succ = X i k.succ * d := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [cornerMat, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
  simp

/-- **The weight of a local type as an index ratio of stabilizers of a vector** in the coordinates of $\Lambda$. -/
theorem locWeightG_eq_relRatio {Q₀ : QuadForm (𝓞 F) (n + 1)} {ρ : F} (hρ : ρ ≠ 0)
    (fr : AdaptedFrame (HilbertModular.formF Q₀) ρ) {c : Fv} (hc : c ≠ 0)
    (M : LocCompSetG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c)
    (h : orthGroup (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))) Fv)
    (hM : locAct v (h : GL (Fin (n + 1)) Fv) (frameLat v fr.g) = M.1) (b : ℕ) (G : GL (Fin (n + 1)) Fv)
    (hG : G = Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g * (h : GL (Fin (n + 1)) Fv)⁻¹ * dMat v hc b) :
    locWeightG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) M =
      relRatio (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (locAct v G (std v)) ⊓
          stabV v (G.val *ᵥ (e₀ : Fin (n + 1) → Fv)))
        (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (std v) ⊓ stabV v (G.val *ᵥ (e₀ : Fin (n + 1) → Fv))) := by
  set gv := Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g
  set hv : GL (Fin (n + 1)) Fv := (h : GL (Fin (n + 1)) Fv)
  set ĝ := gv * hv⁻¹
  have hframe := frame_local v fr
  have hhO : hv⁻¹ ∈ orthGroup (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))) Fv := by
    rw [← Subgroup.coe_inv]; exact (h⁻¹).2
  have hĝ : ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)).compMat ĝ.val =
      (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))).map (algebraMap F Fv) := by
    rw [Units.val_mul, ← compMat_mul, hframe]
    exact (mem_orthGroup_iff_compMat v _ _).mp hhO
  have hinj : Function.Injective (MulAut.conj ĝ).toMonoidHom := (MulAut.conj ĝ).injective
  have hKL : ∀ Λ' : Submodule 𝔬 (Fin (n + 1) → Fv),
      (KL v ((splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))).map (algebraMap F Fv)) Λ').map
        (MulAut.conj ĝ).toMonoidHom = KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (locAct v ĝ Λ') := by
    intro Λ'; rw [KL_locAct, hĝ]
  have hΛ : locAct v ĝ M.1 = std v := by
    rw [← hM, frameLat_eq, ← locAct_mul, ← locAct_mul]
    show locAct v (gv * hv⁻¹ * hv * gv⁻¹) (std v) = std v
    rw [inv_mul_cancel_right, mul_inv_cancel, locAct_one]
  have hDe : (dMat v hc b).val *ᵥ (e₀ : Fin (n + 1) → Fv) = c • e₀ := by
    rw [dMat_val, show (e₀ : Fin (n + 1) → Fv) = Fin.cons 1 0 from rfl, cornerMat_mulVec, mulVec_zero, mul_one]
    funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have hD : ĝ.val *ᵥ (c • (e₀ : Fin (n + 1) → Fv)) = G.val *ᵥ (e₀ : Fin (n + 1) → Fv) := by
    rw [hG, Units.val_mul (ĝ) (dMat v hc b), ← mulVec_mulVec, hDe]
  show relRatio (stdStab _ v) (stabilizer _ M) = _
  rw [← relRatio_map (embO_injective v ρ _), map_stdStab_eq v ρ _ hρ hc b, map_stabilizer_eq v ρ _ hρ hc M,
    ← relRatio_map hinj, Subgroup.map_inf_eq _ _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj, hKL, hKL]
  have hs : (stabV v (c • (e₀ : Fin (n + 1) → Fv))).map (MulAut.conj ĝ).toMonoidHom =
      stabV v (G.val *ᵥ (e₀ : Fin (n + 1) → Fv)) := by rw [stabV_map_conj, hD]
  have hl : locAct v ĝ (locAct v (dMat v hc b) (std v)) = locAct v G (std v) := by
    rw [← locAct_mul, hG]
  rw [hs, hl, hΛ]

/-- **The weight of a local type, by REL and the $\alpha$ law** (any prime where `AlphaLawAt` holds): for a type $M = h\Lambda$
($\Lambda$ the frame lattice, $h \in O(Q)(F_\mathfrak p)$) of the vector $c\,e_0$, with $\hat y = gh^{-1}(c\,e_0) \in \mathfrak o_\mathfrak p^{n+1}$ (the point of the
$K$-orbit in the coordinates of $\Lambda$) and $t = c^2\rho$:
$$w(M)\,\beta(Q_0)\,q^{kn} = N_{k,r}(K\hat y)\,\|\det g\|^{n+1}\|c\|^{n+1}q^{en}\,\beta(Q_0')$$
for all large $r$, $k$. *Proof:* the split sublattice $h^{-1}(\mathfrak o\,c e_0\oplus\varpi^b\mathfrak o^n) \subseteq \Lambda$ ($b$ large) and `perY`; the weight
is the index ratio of the stabilizers of $\hat y$ (`map_stdStab_eq`, `map_stabilizer_eq`, conjugation by $gh^{-1}$); the
scaling of $\beta(\varpi^{2b}Q_0')$ cancels $\|\varpi^b\|^{n(n+1)}$. -/
theorem locWeightG_frame {Q₀ : QuadForm (𝓞 F) (n + 1)} (hQ₀ : Q₀.Nondegenerate) {ρ : F} (hρ : ρ ≠ 0)
    (fr : AdaptedFrame (HilbertModular.formF Q₀) ρ)
    (hlaw : ∀ (P : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬) (hP : P.det ≠ 0), AlphaLawAt v (NF.Qp v Q₀) P hP)
    {c : Fv} (hc : c ≠ 0) (M : LocCompSetG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c)
    (h : orthGroup (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))) Fv)
    (hM : locAct v (h : GL (Fin (n + 1)) Fv) (frameLat v fr.g) = M.1)
    (yo : Fin (n + 1) → 𝔬)
    (hy : (fun i => (yo i : Fv)) = (Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g).val *ᵥ
      ((h⁻¹ : orthGroup _ Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (c • (e₀ : Fin (n + 1) → Fv)))
    {tt : 𝔬} (hto : ((tt : 𝔬) : Fv) = c ^ 2 * algebraMap F Fv ρ) (hto0 : tt ≠ 0) {e : ℕ}
    (he : NF.π v ^ e ∣ 2 * tt) (he' : ¬ NF.π v ^ (e + 1) ∣ 2 * tt) :
    ∃ r₀ : ℕ, ∀ r, r₀ ≤ r → ∀ᶠ k in Filter.atTop,
      locWeightG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) M * localDensityForm (NF.Qp v Q₀) (NF.Qp v Q₀) (NF.π v) *
          (q 𝔬 : ℝ) ^ (k * n) =
        nearCount (NF.Qp v Q₀) (NF.π v) tt k r
            (orbitOf (repStd v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv))) ⊤ yo) *
          (‖(algebraMap F Fv fr.g.val.det)‖ ^ (n + 1) * ‖c‖ ^ (n + 1) * (q 𝔬 : ℝ) ^ (e * n) *
            localDensityForm (NF.Qp v fr.Q') (NF.Qp v fr.Q') (NF.π v)) := by
  classical
  have hπ := NF.irreducible_π v
  set Qo := NF.Qp v Q₀
  set Q'o := NF.Qp v fr.Q'
  set Qov := Qo.map (algebraMap 𝔬 Fv)
  set gv := Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g
  set hv : GL (Fin (n + 1)) Fv := (h : GL (Fin (n + 1)) Fv)
  set ĝ := gv * hv⁻¹
  have hQo : Qo.Nondegenerate := NF.nondegenerate_Qp v hQ₀
  have hQF₀ : (HilbertModular.formF Q₀).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ₀
  have hQ'₀ : fr.Q'.Nondegenerate := fr.nondegenerate hQF₀ hρ
  have hQ'o : Q'o.Nondegenerate := NF.nondegenerate_Qp v hQ'₀
  -- the frame over `F_v`
  have hframe : Qov.compMat gv.val = (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))).map (algebraMap F Fv) :=
    frame_local v fr
  have hhO : hv⁻¹ ∈ orthGroup (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))) Fv := by
    rw [← Subgroup.coe_inv]; exact (h⁻¹).2
  have hĝ : Qov.compMat ĝ.val = (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))).map (algebraMap F Fv) := by
    rw [Units.val_mul, ← compMat_mul, hframe]
    exact (mem_orthGroup_iff_compMat v _ _).mp hhO
  -- the integral matrix of the split sublattice
  obtain ⟨b, A, hA⟩ := exists_scale_integral v ĝ.val
  set ϖ : Fv := ((NF.π v : 𝔬) : Fv)
  set D := dMat v hc b
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬 := Matrix.of fun i k => Fin.cases (yo i) (fun k' => A i k'.succ) k
  have hyc : ∀ i, (yo i : Fv) = ĝ.val i 0 * c := by
    intro i
    have := congrFun hy i
    rw [this, mulVec_mulVec, mulVec_smul, e₀_eq_single, mulVec_single_one]
    simp only [Pi.smul_apply, smul_eq_mul, ĝ, Units.val_mul, hv, Subgroup.coe_inv]
    rw [mul_comm]; rfl
  have hPmap : P.map (algebraMap 𝔬 Fv) = (ĝ * D).val := by
    refine Matrix.ext fun i k => ?_
    rw [Units.val_mul, dMat_val]
    refine Fin.cases ?_ (fun k' => ?_) k
    · rw [mul_cornerMat_apply_zero, ← hyc]; rfl
    · rw [mul_cornerMat_apply_succ]
      have := congrFun (congrFun hA i) k'.succ
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
      show ((A i k'.succ : 𝔬) : Fv) = _
      rw [show ((A i k'.succ : 𝔬) : Fv) = algebraMap 𝔬 Fv (A i k'.succ) from rfl, this, mul_comm]
  have hPdet : P.det ≠ 0 := by
    intro h0
    have : (P.map (algebraMap 𝔬 Fv)).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    rw [hPmap] at this
    exact ((ĝ * D).isUnit.map Matrix.detMonoidHom).ne_zero this
  have hglP : glOf v P hPdet = ĝ * D := Units.ext (by rw [glOf_val, hPmap])
  have hPe : P *ᵥ (e₀ : Fin (n + 1) → 𝔬) = yo := by
    rw [e₀_eq_single, mulVec_single_one]; funext i; rfl
  -- the split form of the sublattice
  have hQ''nd : (((NF.π v) ^ b) ^ 2 • Q'o).Nondegenerate :=
    nondegenerate_smul hQ'o (pow_ne_zero _ (pow_ne_zero _ hπ.ne_zero))
  have hsplit : Qo.compMat P = splitForm tt (((NF.π v) ^ b) ^ 2 • Q'o) := by
    apply quadForm_map_o_inj v
    rw [← map_compMat, hPmap, Units.val_mul, ← compMat_mul, hĝ, map_splitForm, map_splitForm, dMat_val,
      splitForm_compMat_corner, compMat_smul_one, map_smul_form, map_Qp_eq]
    congr 1
    rw [show algebraMap 𝔬 Fv tt = ((tt : 𝔬) : Fv) from rfl, hto]
  obtain ⟨r₀, hr₀⟩ := perY v Qo hQo _ hQ''nd hto0 P hPdet hsplit (hlaw P hPdet) he he'
  refine ⟨r₀, fun r hr => ?_⟩
  filter_upwards [hr₀ r hr] with k hk
  rw [hPe] at hk
  have hw := locWeightG_eq_relRatio v hρ fr hc M h hM b (glOf v P hPdet) (by rw [hglP])
  rw [hw, hk]
  -- the determinant and the scaling of `β`
  have hdetP : ‖((P.det : 𝔬) : Fv)‖ = ‖algebraMap F Fv fr.g.val.det‖ * ‖c‖ * ‖ϖ‖ ^ (b * n) := by
    have e1 : ((P.det : 𝔬) : Fv) = (ĝ * D).val.det := by
      rw [← hPmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    have hhdet : ‖hv⁻¹.val.det‖ = 1 := by
      have hH := (mem_orthGroup _).mp hhO
      have hd := congrArg Matrix.det hH
      rw [det_mul, det_mul, det_transpose] at hd
      have hHd : ((splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))).hessian.map (algebraMap F Fv)).det ≠ 0 := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_hessian_splitForm, map_ne_zero]
        refine mul_ne_zero (mul_ne_zero two_ne_zero hρ) ?_
        have hQF'nd : (fr.Q'.map (algebraMap (𝓞 F) F)).Nondegenerate := by
          rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
          exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ'₀
        exact hQF'nd
      have h1 : hv⁻¹.val.det * hv⁻¹.val.det = 1 := by
        have : (hv⁻¹.val.det * hv⁻¹.val.det - 1) *
            ((splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))).hessian.map (algebraMap F Fv)).det = 0 := by
          linear_combination hd
        rcases mul_eq_zero.mp this with h' | h'
        · linear_combination h'
        · exact absurd h' hHd
      have h2' : ‖hv⁻¹.val.det‖ * ‖hv⁻¹.val.det‖ = 1 := by rw [← norm_mul, h1, norm_one]
      nlinarith [norm_nonneg (hv⁻¹.val.det)]
    rw [e1, Units.val_mul, Units.val_mul, det_mul, det_mul, norm_mul, norm_mul, hhdet, mul_one, dMat_val,
      det_cornerMat, det_smul, det_one, mul_one, norm_mul, norm_pow, norm_pow, Fintype.card_fin, ← pow_mul,
      mul_comm b n]
    rw [show (gv.val.det) = algebraMap F Fv fr.g.val.det by
      rw [RingHom.map_det]; rfl]
    ring
  have hϖ : ‖ϖ‖ = (q 𝔬 : ℝ)⁻¹ := by
    have := norm_coe_of_pow_dvd v (e := 1) (x := NF.π v) (by rw [pow_one]) (fun h' => by
      obtain ⟨u, hu⟩ := h'
      have : NF.π v * (NF.π v * u - 1) = 0 := by linear_combination -hu
      rcases mul_eq_zero.mp this with h'' | h''
      · exact hπ.ne_zero h''
      · exact hπ.not_isUnit ⟨⟨NF.π v, u, by linear_combination h'', by linear_combination h''⟩, rfl⟩)
    rw [this, pow_one]
  have h2b : NF.π v ^ (2 * b) ∣ (NF.π v ^ b) ^ 2 := by rw [← pow_mul, mul_comm]
  have h2b' : ¬ NF.π v ^ (2 * b + 1) ∣ (NF.π v ^ b) ^ 2 := by
    rw [← pow_mul, mul_comm b 2]
    intro ⟨u, hu⟩
    rw [pow_succ, mul_assoc] at hu
    have : NF.π v ^ (2 * b) * (NF.π v * u - 1) = 0 := by linear_combination -hu
    rcases mul_eq_zero.mp this with h'' | h''
    · exact pow_ne_zero _ hπ.ne_zero h''
    · exact hπ.not_isUnit ⟨⟨NF.π v, u, by linear_combination h'', by linear_combination h''⟩, rfl⟩
  rw [localDensityForm_smul Q'o hQ'o hπ h2b h2b', hdetP, hϖ]
  have hq : (0 : ℝ) < q 𝔬 := Nat.cast_pos.mpr q_pos
  have hT : 2 * b * (n * (n + 1) / 2) = b * n * (n + 1) := by
    obtain ⟨t', ht'⟩ := (Nat.even_mul_succ_self n).two_dvd
    rw [ht', Nat.mul_div_cancel_left t' two_pos, mul_assoc b n, ht']; ring
  rw [hT]
  have hX : ((q 𝔬 : ℝ)⁻¹ ^ (b * n)) ^ (n + 1) * (q 𝔬 : ℝ) ^ (b * n * (n + 1)) = 1 := by
    rw [← pow_mul, inv_pow, inv_mul_cancel₀ (pow_pos hq _).ne']
  rw [mul_pow, mul_pow]
  linear_combination (nearCount Qo (NF.π v) tt k r (orbitOf (repStd v Qov) ⊤ yo) *
    ‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1) * ‖c‖ ^ (n + 1) * (q 𝔬 : ℝ) ^ (e * n) *
    localDensityForm Q'o Q'o (NF.π v) : ℝ) * hX

/-- The stabilizer of the frame lattice $\Lambda = g^{-1}\mathfrak o_\mathfrak p^{n+1}$ in $O(\langle\rho\rangle\perp Q')$, in the coordinates of $\Lambda$, is
$K(\mathfrak o_\mathfrak p^{n+1}) \subseteq O(Q_0)$. -/
theorem conj_mem_KL_std_iff {Q₀ : QuadForm (𝓞 F) (n + 1)} {ρ : F} (fr : AdaptedFrame (HilbertModular.formF Q₀) ρ)
    (k : GL (Fin (n + 1)) Fv) :
    Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g * k * (Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g)⁻¹ ∈
        KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (std v) ↔
      k ∈ orthGroup (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))) Fv ∧
        locAct v k (frameLat v fr.g) = frameLat v fr.g := by
  set gv := Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g
  have hstd : (std v : Submodule 𝔬 (Fin (n + 1) → Fv)) = locAct v gv (frameLat v fr.g) := by
    rw [frameLat_eq, ← locAct_mul, mul_inv_cancel, locAct_one]
  rw [hstd, KL_locAct, frame_local, Subgroup.mem_map_equiv (f := MulAut.conj gv), MulAut.conj_symm_apply,
    mem_KL, mem_orthGroup_iff_compMat]
  have : gv⁻¹ * (gv * k * gv⁻¹) * gv = k := by group
  rw [this]

end FrameData

/-! ### The local orbital identity from the $\alpha$ law -/

section MainLocal

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The values of $\langle\rho\rangle\perp Q'$ on the frame lattice are the values of $Q_0$ on $\mathfrak o_\mathfrak p^{n+1}$. -/
theorem frame_eval {Q₀ : QuadForm (𝓞 F) (n + 1)} {ρ : F} (fr : AdaptedFrame (HilbertModular.formF Q₀) ρ)
    (u : Fin (n + 1) → 𝔬) :
    ((splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))).map (algebraMap F Fv)).eval
        ((Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g)⁻¹.val *ᵥ fun i => (u i : Fv)) =
      (((NF.Qp v Q₀).eval u : 𝔬) : Fv) := by
  rw [← frame_local v fr, eval_compMat, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_mulVec]
  exact eval_map_comp (algebraMap 𝔬 Fv) _ u

theorem eval_orth {N : ℕ} (Q : QuadForm F N) (g : orthGroup Q Fv) (z : Fin N → Fv) :
    (Q.map (algebraMap F Fv)).eval ((g : GL (Fin N) Fv).val *ᵥ z) = (Q.map (algebraMap F Fv)).eval z := by
  rw [← eval_compMat, (mem_orthGroup_iff_compMat v Q _).mp g.2]

/-- **The local orbital identity at every prime where the $\alpha$ law holds** (Weil 1982, §3.4 and §4.5, p. 109 [unverified];
lattice change, no Haar measure). For $Q_0$ over $\mathcal O_F$ nondegenerate, $\rho \ne 0$ and any adapted frame
$Q_0\circ g = \langle\rho\rangle\perp Q_0'$: if the $\alpha$ transformation law holds for $Q_0\otimes\mathfrak o_\mathfrak p$ (`AlphaLawAt`, for every $P$),
then `OrbitalLocalIdentityAt v Q₀ fr`. *Proof:* the local types of $\varpi^je_0$ correspond to the $O(\mathfrak o_\mathfrak p^{n+1})$-orbits on
$\{y : Q_0(y) = \rho\varpi^{2j}\}$ (Witt's involutions, as in `OrbitalEuler`); each weight is $N(\text{orbit})$ times a constant (`locWeightG_frame`); the
orbits partition the level set mod $\varpi^k$ (`repCount_eq_sum_nearCount`). -/
@[kb "weil1982" "§3.4 and §4.5, p. 109 (the local orbital identity at the non-standard primes) [unverified]"]
theorem orbitalLocalIdentityAt_of_law (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ₀ : Q₀.Nondegenerate) {ρ : F} (hρ : ρ ≠ 0)
    (fr : AdaptedFrame (HilbertModular.formF Q₀) ρ)
    (hlaw : ∀ (P : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬) (hP : P.det ≠ 0), AlphaLawAt v (NF.Qp v Q₀) P hP) :
    OrbitalLocalIdentityAt v Q₀ fr := by
  classical
  refine ⟨fun j => ?_⟩
  have hπ := NF.irreducible_π v
  set gv := Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g
  set c : Fv := unifV v ^ j
  have hϖ0 : unifV v ≠ 0 := fun h => hπ.ne_zero (Subtype.ext (by simpa [unifV] using h))
  have hc : c ≠ 0 := zpow_ne_zero _ hϖ0
  set Qo := NF.Qp v Q₀
  set Qov := Qo.map (algebraMap 𝔬 Fv)
  have hQo : Qo.Nondegenerate := NF.nondegenerate_Qp v hQ₀
  have hc2 : c ^ 2 * algebraMap F Fv ρ = algebraMap F Fv ρ * unifV v ^ (2 * j) := by
    rw [mul_comm, ← zpow_natCast, ← _root_.zpow_mul]; ring_nf
  -- the value of `Q` at `c e₀` is the value of `Q₀` at an integral vector for every local type
  have hval : ∀ M : LocCompSetG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c,
      ∃ (h : orthGroup (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))) Fv) (yo : Fin (n + 1) → 𝔬),
        locAct v (h : GL (Fin (n + 1)) Fv) (frameLat v fr.g) = M.1 ∧
        (fun i => (yo i : Fv)) = gv.val *ᵥ ((h⁻¹ : orthGroup _ Fv) : GL (Fin (n + 1)) Fv).val *ᵥ
          (c • (e₀ : Fin (n + 1) → Fv)) ∧
        (((Qo.eval yo : 𝔬)) : Fv) = c ^ 2 * algebraMap F Fv ρ := by
    intro M
    obtain ⟨h, hh⟩ := M.2.1
    have hx := M.2.2
    rw [← hh, mem_locAct] at hx
    obtain ⟨y, hy, hhy⟩ := hx
    rw [frameLat_eq, mem_locAct] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨uo, rfl⟩ := integral_of_mem_std v hu
    refine ⟨h, uo, hh, ?_, ?_⟩
    · have e1 : ((h⁻¹ : orthGroup _ Fv) : GL (Fin (n + 1)) Fv).val *ᵥ ((h : GL (Fin (n + 1)) Fv).val *ᵥ
          (gv⁻¹.val *ᵥ fun i => (uo i : Fv))) = gv⁻¹.val *ᵥ fun i => (uo i : Fv) := by
        rw [mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel, Units.val_one, one_mulVec]
      rw [← hhy, e1, mulVec_inv_mulVec]
    · rw [← frame_eval v fr uo, ← eval_orth v _ h, hhy, eval_smul_gen, map_splitForm, eval_splitForm_e₀']
  set tFv := algebraMap F Fv ρ * unifV v ^ (2 * j)
  by_cases ht : Valued.v tFv ≤ 1
  swap
  · -- no local types
    have hE : IsEmpty (LocTypesG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c) := by
      refine ⟨fun τ => ht ?_⟩
      obtain ⟨_, yo, -, -, hyo⟩ := hval τ.out
      rw [← hc2, ← hyo]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (Qo.eval yo).2
    have hW : locW v fr j = 0 := by
      unfold locW; rw [locTypeSumG, finsum_of_isEmpty]
    have hβ : betaZ v Q₀ tFv = 0 := by unfold betaZ; rw [dif_neg ht]
    rw [hW, hβ]; ring
  set tt : 𝔬 := ⟨tFv, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ht⟩
  have htt : ((tt : 𝔬) : Fv) = c ^ 2 * algebraMap F Fv ρ := by rw [hc2]
  have htt0 : tt ≠ 0 := by
    intro h0
    have : ((tt : 𝔬) : Fv) = 0 := by rw [h0]; rfl
    rw [htt] at this
    exact mul_ne_zero (pow_ne_zero 2 hc) ((map_ne_zero _).mpr hρ) this
  have h2 := NF.two_ne_zero' v
  obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h2 htt0)
  have h4 : (4 * tt : 𝔬) ≠ 0 := by
    rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero h2 h2) htt0
  obtain ⟨f, hf, hf'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ h4
  choose hτ yo hτM hτy hτQ using fun τ : LocTypesG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c =>
    hval τ.out
  have hyo : ∀ τ, Qo.eval (yo τ) = tt := fun τ => Subtype.ext (by rw [hτQ τ, htt])
  have hinvx : ∀ τ, (((hτ τ)⁻¹ : orthGroup _ Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (c • (e₀ : Fin (n + 1) → Fv)) =
      gv⁻¹.val *ᵥ fun i => (yo τ i : Fv) := by
    intro τ
    rw [hτy τ, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hm2 : algebraMap F Fv (2 * ρ) ≠ 0 := by rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hρ
  have hw := fun τ : LocTypesG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c =>
    locWeightG_frame v hQ₀ hρ fr hlaw hc τ.out (hτ τ) (hτM τ) (yo τ) (hτy τ) htt htt0 he he'
  choose r₀ hr₀ using hw
  -- disjointness of the orbits of the types
  have hdisj : ∀ r, f + 1 ≤ r → ∀ τ τ', ∀ a ∈ orbitOf (repStd v Qov) ⊤ (yo τ),
      ∀ a' ∈ orbitOf (repStd v Qov) ⊤ (yo τ'), (∀ i, NF.π v ^ r ∣ a i - a' i) → τ = τ' := by
    rintro r hr τ τ' a ⟨κ, -, ha⟩ a' ⟨κ', -, ha'⟩ haa'
    have hQa : Qo.eval a = tt := by rw [← ha, ← eval_compMat, compMat_repStd v rfl, hyo τ]
    have hQa' : Qo.eval a' = tt := by rw [← ha', ← eval_compMat, compMat_repStd v rfl, hyo τ']
    obtain ⟨T, hT, hTa, -⟩ := exists_openMat hπ Qo htt0 hf hf' (s := r) hr hQa hQa'
      (fun i => by rw [← dvd_neg, neg_sub]; exact haa' i)
    obtain ⟨τT, hτT⟩ := exists_repStd_eq v rfl hQo T hT
    set κ₀ := κ'⁻¹ * τT * κ
    have hκ₀ : repStd v Qov κ₀ *ᵥ yo τ = yo τ' := by
      rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, ha, hτT, hTa, ← ha',
        mulVec_inv_mulVec' (repStd v Qov) κ']
    have hκ₀v : (κ₀ : GL (Fin (n + 1)) Fv).val *ᵥ (fun i => (yo τ i : Fv)) = fun i => (yo τ' i : Fv) := by
      rw [← repStd_map, ← coe_mulVec_o, hκ₀]
    set k₀ := gv⁻¹ * (κ₀ : GL (Fin (n + 1)) Fv) * gv
    have hk₀ : gv * k₀ * gv⁻¹ = (κ₀ : GL (Fin (n + 1)) Fv) := by simp only [k₀]; group
    have hk₀mem := (conj_mem_KL_std_iff v fr k₀).mp (by rw [hk₀]; exact κ₀.2)
    set γ : orthGroup (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))) Fv := hτ τ' * ⟨k₀, hk₀mem.1⟩ * (hτ τ)⁻¹
    have hγc : (γ : GL (Fin (n + 1)) Fv).val *ᵥ (c • (e₀ : Fin (n + 1) → Fv)) = c • e₀ := by
      simp only [γ, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
      rw [hinvx τ]
      have : k₀.val *ᵥ (gv⁻¹.val *ᵥ fun i => (yo τ i : Fv)) = gv⁻¹.val *ᵥ fun i => (yo τ' i : Fv) := by
        simp only [k₀, Units.val_mul, ← mulVec_mulVec]
        rw [mulVec_inv_mulVec, hκ₀v]
      show (hτ τ' : GL (Fin (n + 1)) Fv).val *ᵥ (k₀.val *ᵥ _) = _
      rw [this, ← hinvx τ', mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
      simp
    have hγ : (γ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
      apply smul_right_injective _ hc
      show c • (_ *ᵥ e₀) = c • e₀
      rw [← mulVec_smul, hγc]
    obtain ⟨a₀, ha₀⟩ := exists_orthEmb_eq ρ _ Fv hm2 γ hγ
    have hmem : τ'.out ∈ orbit (orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) τ.out := by
      refine ⟨a₀, Subtype.ext ?_⟩
      rw [LocCompSetG.smul_val, ha₀, ← hτM τ, ← hτM τ', ← locAct_mul]
      simp only [γ, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right, locAct_mul]
      rw [hk₀mem.2]
    have : (Quotient.mk'' τ'.out : LocTypesG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c) =
        Quotient.mk'' τ.out := Quotient.sound' hmem
    rw [Quotient.out_eq', Quotient.out_eq'] at this
    exact this.symm
  have hfin : Finite (LocTypesG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c) := by
    have := finite_vec (ι := Fin (n + 1)) (NF.π v) hπ (f + 1)
    refine Finite.of_injective (fun τ => redI (NF.π v) (f + 1) (yo τ)) fun τ τ' hττ => ?_
    exact hdisj (f + 1) le_rfl τ τ' (yo τ) ⟨1, Subgroup.mem_top 1, by simp⟩ (yo τ')
      ⟨1, Subgroup.mem_top 1, by simp⟩ ((redI_eq_iff _ _ _ _).mp hττ)
  let _ : Fintype (LocTypesG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c) := Fintype.ofFinite _
  -- every solution lies in the orbit of some type
  have hcover : ∀ y, Qo.eval y = tt → ∃ τ, y ∈ orbitOf (repStd v Qov) ⊤ (yo τ) := by
    intro y hy
    set w := gv⁻¹.val *ᵥ (fun i => (y i : Fv))
    have hwΛ : w ∈ frameLat v fr.g := by rw [frameLat_eq]; exact ⟨_, coe_mem_std v y, rfl⟩
    have hQw : (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))).evalIn Fv w = c ^ 2 * algebraMap F Fv ρ := by
      rw [evalIn_eq_eval_map, frame_eval v fr y, hy, htt]
    obtain ⟨σ, hσσ, hσe⟩ := exists_inv_e₀ v ρ _ hρ _ (evalIn_smul_inv v ρ _ hc w hQw)
    have hσx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ (c • (e₀ : Fin (n + 1) → Fv)) = w := by
      rw [mulVec_smul, hσe, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hσw : (σ : GL (Fin (n + 1)) Fv).val *ᵥ w = c • e₀ := by
      rw [← hσx, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, hσσ]; simp
    let M' : LocCompSetG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c :=
      ⟨locAct v (σ : GL (Fin (n + 1)) Fv) (frameLat v fr.g), ⟨σ, rfl⟩, ⟨w, hwΛ, hσw⟩⟩
    set τ : LocTypesG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) c := Quotient.mk'' M'
    obtain ⟨a, ha⟩ : τ.out ∈ orbit (orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) M' :=
      Quotient.exact' (Quotient.out_eq' τ)
    set k : orthGroup (splitForm ρ (fr.Q'.map (algebraMap (𝓞 F) F))) Fv := (hτ τ)⁻¹ * orthEmb ρ _ Fv a * σ
    have h1 : locAct v (orthEmb ρ _ Fv a : GL (Fin (n + 1)) Fv)
        (locAct v (σ : GL (Fin (n + 1)) Fv) (frameLat v fr.g)) = τ.out.1 := by
      rw [← ha]; rfl
    have hkΛ : locAct v (k : GL (Fin (n + 1)) Fv) (frameLat v fr.g) = frameLat v fr.g := by
      simp only [k, Subgroup.coe_mul, Subgroup.coe_inv, locAct_mul]
      rw [h1, ← hτM τ, locAct_inv_locAct]
    have hkw : (k : GL (Fin (n + 1)) Fv).val *ᵥ w = (((hτ τ)⁻¹ : orthGroup _ Fv) : GL (Fin (n + 1)) Fv).val *ᵥ
        (c • (e₀ : Fin (n + 1) → Fv)) := by
      simp only [k, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
      rw [hσw, orthEmb_mulVec_smul_e₀]
    set κ : GL (Fin (n + 1)) Fv := gv * (k : GL (Fin (n + 1)) Fv) * gv⁻¹
    have hκ : κ ∈ KL v Qov (std v) := (conj_mem_KL_std_iff v fr _).mpr ⟨k.2, hkΛ⟩
    have hκy : κ.val *ᵥ (fun i => (y i : Fv)) = fun i => (yo τ i : Fv) := by
      simp only [κ, Units.val_mul, ← mulVec_mulVec]
      rw [show gv⁻¹.val *ᵥ (fun i => (y i : Fv)) = w from rfl, hkw, hinvx τ, mulVec_inv_mulVec]
    refine ⟨τ, ⟨⟨κ, hκ⟩⁻¹, Subgroup.mem_top _, ?_⟩⟩
    apply coe_o_injective v
    show (fun i => ((repStd v Qov ⟨κ, hκ⟩⁻¹ *ᵥ yo τ) i : Fv)) = fun i => (y i : Fv)
    rw [coe_mulVec_o, repStd_map, ← hκy]
    show κ⁻¹.val *ᵥ (κ.val *ᵥ _) = _
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  -- the levels `r` and `k`
  set r := Finset.univ.sup r₀ + f + 1
  have hrr : ∀ τ, r₀ τ ≤ r := fun τ => by
    have := Finset.le_sup (f := r₀) (Finset.mem_univ τ); omega
  have hev := Filter.eventually_all.mpr fun τ => hr₀ τ r (hrr τ)
  obtain ⟨k, hk, hkβ, hkge⟩ := (hev.and ((localDensity_eventually_eq Qo hQo (NF.π v) hπ tt htt0 h2).and
    (Filter.eventually_ge_atTop (r + e + 2 * e + 1)))).exists
  have hsum := repCount_eq_sum_nearCount hπ Qo he he' (fun τ => orbitOf (repStd v Qov) ⊤ (yo τ)) hcover
    (hdisj r (by omega)) (k := k) (by omega) (by omega)
  set X := ‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1) * ‖c‖ ^ (n + 1) * (q 𝔬 : ℝ) ^ (e * n) *
    localDensityForm (NF.Qp v fr.Q') (NF.Qp v fr.Q') (NF.π v)
  have hmain : locW v fr j * localDensityForm Qo Qo (NF.π v) * (q 𝔬 : ℝ) ^ (k * n) =
      (LocalDensity.DVR.repCount Qo (NF.π v) k tt : ℝ) * X := by
    unfold locW
    rw [locTypeSumG, finsum_eq_sum_of_fintype, Finset.sum_mul, Finset.sum_mul, hsum, Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun τ _ => hk τ
  have hq : (0 : ℝ) < q 𝔬 := Nat.cast_pos.mpr q_pos
  rw [show k * (n + 1 - 1) = k * n by rw [Nat.add_sub_cancel]] at hkβ
  have hkey : locW v fr j * localDensityForm Qo Qo (NF.π v) = localDensity Qo (NF.π v) tt * X := by
    rw [← hkβ]
    have hZ : (0 : ℝ) < (q 𝔬 : ℝ) ^ (k * n) := pow_pos hq _
    field_simp
    linear_combination hmain
  -- the norms
  have hNc : ‖c‖ = (q 𝔬 : ℝ) ^ (-j) := by
    rw [norm_unifV_zpow, ← NF.q_completion]
  have h2tt : ‖(2 : Fv) * algebraMap F Fv ρ‖ * ‖c‖ ^ 2 = ((q 𝔬 : ℝ) ^ e)⁻¹ := by
    rw [← norm_coe_of_pow_dvd v he he', ← norm_pow, ← norm_mul]
    congr 1
    push_cast
    rw [htt, show ((2 : 𝔬) : Fv) = 2 from rfl]
    ring
  have hα : NF.siegelDensity v Q₀ Q₀ = 1 / 2 * localDensityForm Qo Qo (NF.π v) := by
    unfold NF.siegelDensity; rw [if_pos rfl, NF.localDensityForm_eq_completion]
  have hα' : NF.siegelDensity v fr.Q' fr.Q' =
      1 / 2 * localDensityForm (NF.Qp v fr.Q') (NF.Qp v fr.Q') (NF.π v) := by
    unfold NF.siegelDensity; rw [if_pos rfl, NF.localDensityForm_eq_completion]
  have hbeta : betaZ v Q₀ tFv = localDensity Qo (NF.π v) tt := by
    unfold betaZ; rw [dif_pos ht]
  rw [hα, hα', hbeta]
  set Q := (q 𝔬 : ℝ)
  have hQ0 : Q ≠ 0 := hq.ne'
  have hNc0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hN2 : ‖(2 : Fv) * algebraMap F Fv ρ‖ = (Q ^ e)⁻¹ / ‖c‖ ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hNc0)]; exact h2tt
  have hfac : ‖c‖ ^ (n + 1) * Q ^ (e * n) * ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n = Q ^ (j * ((n : ℤ) - 1)) := by
    rw [hN2, hNc]
    have e1 : (Q ^ (-j)) ^ (n + 1) = Q ^ (-j * ((n : ℤ) + 1)) := by
      rw [← zpow_natCast, ← _root_.zpow_mul]; push_cast; ring_nf
    have e2 : Q ^ (e * n) = Q ^ ((e : ℤ) * n) := by rw [← zpow_natCast]; push_cast; ring_nf
    have e3 : ((Q ^ e)⁻¹ / (Q ^ (-j)) ^ 2) ^ n = Q ^ ((2 * j - e) * (n : ℤ)) := by
      rw [← zpow_natCast Q e, ← _root_.zpow_neg, ← zpow_natCast (Q ^ (-j)) 2, ← _root_.zpow_mul,
        ← zpow_sub₀ hQ0, ← zpow_natCast, ← _root_.zpow_mul]
      congr 1; push_cast; ring
    rw [e1, e2, e3, ← zpow_add₀ hQ0, ← zpow_add₀ hQ0]
    congr 1; ring
  have hDg : ‖algebraMap F Fv fr.g.val.det‖ ≠ 0 := by
    rw [norm_ne_zero_iff, map_ne_zero]
    exact (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
  rw [show locW v fr j * (1 / 2 * localDensityForm Qo Qo (NF.π v)) * ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n *
      (‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1))⁻¹ =
      1 / 2 * (locW v fr j * localDensityForm Qo Qo (NF.π v)) * ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n *
      (‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1))⁻¹ by ring, hkey, ← hfac]
  simp only [X]
  field_simp
  ring

/-- **The local orbital identity at every non-dyadic prime, for every frame** (`alphaLaw_odd` and
`orbitalLocalIdentityAt_of_law`): unconditional. -/
@[kb "weil1982" "§3.4 and §4.5, p. 109 (the local orbital identity at p ∤ 2, every frame) [unverified]"]
theorem orbitalLocalIdentityAt_odd (h2 : ¬ NF.π v ∣ 2) (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ₀ : Q₀.Nondegenerate)
    {ρ : F} (hρ : ρ ≠ 0) (fr : AdaptedFrame (HilbertModular.formF Q₀) ρ) : OrbitalLocalIdentityAt v Q₀ fr :=
  orbitalLocalIdentityAt_of_law v Q₀ hQ₀ hρ fr fun P hP =>
    alphaLaw_odd v h2 (n + 1) (NF.Qp v Q₀) P hP (NF.nondegenerate_Qp v hQ₀)

end MainLocal

/-! ### The orbital Euler product and $\tau = 2$ with only the dyadic input -/

section Headline

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

open QuadFormsKB.SphericalZeta QuadFormsKB.SphericalFibration HilbertModular

/-- **Input: the $\alpha$ transformation law at the dyadic places** for $Q_0\otimes\mathfrak o_\mathfrak p$ (Weil 1982, §2.4 and §3.4:
the Haar measure of $O(\Lambda)$ is $\propto \alpha(\Lambda)\,|\det\Lambda|^{(N+1)/2}$ [unverified]; Kitaoka 1993, §5.6 [unverified]).

Field:
- `law`: at every prime $\mathfrak p \mid 2$ and for every integral $P$ with $\det P \ne 0$, `AlphaLawAt v (NF.Qp v Q₀) P`, i.e.
  $r\big(O(P\mathfrak o_\mathfrak p^{n+1}), O(\mathfrak o_\mathfrak p^{n+1})\big)\,\beta_\mathfrak p(Q_0) = \beta_\mathfrak p(Q_0\circ P)\,\|\det P\|^{n+2}$.

*Status and hygiene.* A statement about one dyadic place at a time (finitely many: $\mathfrak p \mid 2$), about the lattices of the one
quadratic space $Q_0\otimes F_\mathfrak p$: index ratios of lattice stabilizers against local self-densities. It mentions no classes, masses
or $\tau$ and is not equivalent to $\tau(SO(V)) = 2$. The same law is **proved** at every $\mathfrak p \nmid 2$ (`alphaLaw_odd`, by
counting), and in general it is the normalization of Weil's gauge-form Haar measures (a route not taken here). The proof
at $\mathfrak p \nmid 2$ uses diagonal Jordan bases and split vectors; at $\mathfrak p \mid 2$ even unimodular (binary) Jordan components have
no split vector, which is why this case is left as the input. -/
@[kb "weil1982" "§2.4 and §3.4 (Haar measures of lattice stabilizers at the dyadic places) [unverified]"]
structure DyadicAlphaLaw (Q₀ : QuadForm (𝓞 F) (n + 1)) : Prop where
  law : ∀ v : HeightOneSpectrum (𝓞 F), NF.π v ∣ 2 →
    ∀ (P : Matrix (Fin (n + 1)) (Fin (n + 1)) (v.adicCompletionIntegers F)) (hP : P.det ≠ 0),
      AlphaLawAt v (NF.Qp v Q₀) P hP

/-- **The input from the dyadic law**: `OrbitalLocalIdentities Q₀` holds given only `DyadicAlphaLaw Q₀`
(every non-dyadic prime by `orbitalLocalIdentityAt_odd`). -/
@[kb "weil1982" "§3.4 and §4.5, p. 109 (local orbital identities at all non-standard primes) [unverified]"]
theorem orbitalLocalIdentities_of_dyadic (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ₀ : Q₀.Nondegenerate)
    (hdy : DyadicAlphaLaw Q₀) : OrbitalLocalIdentities Q₀ :=
  ⟨fun ρ fr v hρ _ => orbitalLocalIdentityAt_of_law v Q₀ hQ₀ hρ fr fun P hP => by
    by_cases h2 : NF.π v ∣ 2
    · exact hdy.law v h2 P hP
    · exact alphaLaw_odd v h2 (n + 1) (NF.Qp v Q₀) P hP (NF.nondegenerate_Qp v hQ₀)⟩

theorem nondegenerate_of_totallyPosDef' {Q₀ : QuadForm (𝓞 F) (n + 1)} (hpd : IsTotallyPosDef (formF Q₀)) :
    Q₀.Nondegenerate := by
  have := hpd.nondegenerate
  rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  exact fun h => this (by rw [h, map_zero])

/-- **The orbital Euler product with only the dyadic input** (`orbitalEulerProduct`, its input
`OrbitalLocalIdentities` discharged at every prime $\mathfrak p \nmid 2$). -/
@[kb "weil1982" "§4.5, p. 109 (the orbital Euler product)"]
theorem orbitalEulerProduct' [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (hdy : DyadicAlphaLaw Q₀) :
    OrbitalEulerProduct Q₀ (tauComp Q₀) :=
  orbitalEulerProduct Q₀ hpd hn (orbitalLocalIdentities_of_dyadic Q₀ (nondegenerate_of_totallyPosDef' hpd) hdy)

/-- **$\tau(SO(V)) = 2$ from the induction hypothesis, with only the dyadic input** (Weil 1982, §4.5, Thm 4.5.1, p. 109). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109 (induction step n → n+1)"]
theorem tamagawaNumberTwo_of_complement' [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (hdy : DyadicAlphaLaw Q₀)
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q') :
    TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_of_complement Q₀ hpd hn
    (orbitalLocalIdentities_of_dyadic Q₀ (nondegenerate_of_totallyPosDef' hpd) hdy) hIH

/-- **The mass formula in rank $n + 1 \ge 5$ from the induction hypothesis, with only the dyadic input.** -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; cf. Kitaoka 1993, Thm 6.8.1 [unverified]"]
theorem massFormula_of_complement' [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (hdy : DyadicAlphaLaw Q₀)
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q') :
    mass (formF Q₀) (stdLat F (n + 1)) = (tamagawaK Q₀)⁻¹ :=
  massFormula_of_complement Q₀ hpd hn
    (orbitalLocalIdentities_of_dyadic Q₀ (nondegenerate_of_totallyPosDef' hpd) hdy) hIH

/-- **Siegel's formula for the number $m$ in rank $n + 1 \ge 5$, with only the dyadic input.** -/
@[kb "weil1982" "§4.5, p. 100 (Siegel's theorem as a consequence of τ = 2), Thm 4.5.1, p. 109"]
theorem siegelFormulaAt_of_complement' [IsPrincipalIdealRing (𝓞 F)] (m₀ : 𝓞 F) (hm : m₀ ≠ 0)
    (Q₀' : QuadForm (𝓞 F) n) (hn : 4 ≤ n) (hpd : IsTotallyPosDef (formF (splitForm m₀ Q₀')))
    (hdy : DyadicAlphaLaw (splitForm m₀ Q₀'))
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q') :
    SiegelFormulaAt (splitForm m₀ Q₀') m₀ :=
  siegelFormulaAt_of_complement m₀ hm Q₀' hn hpd
    (orbitalLocalIdentities_of_dyadic _ (nondegenerate_of_totallyPosDef' hpd) hdy) hIH

end Headline

end QuadFormsKB.Tamagawa
