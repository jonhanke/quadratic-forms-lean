/-
# Hanke, AWS 2009 notes, Lemma 4.5.1: gluing of lattices over ℚ (proved)

**Layer:** the concrete lattices of `AWS/Adelic.lean`: `Lat n` (sets $g\mathbb{Z}^n \subset \mathbb{Q}^n$,
$g \in \mathrm{GL}_n(\mathbb{Q})$) and `LocLat p n` (sets $g\mathbb{Z}_p^n \subset \mathbb{Q}_p^n$).

**Proves** the existence half of Lemma 4.5.1 of J. Hanke, *Quadratic Forms and Automorphic Forms*
(bibkey `hanke2011aws`, §4.5, p. 61), the input `LatticeGluing n` of D15–D16, which the notes cite from
Shimura, *Arithmetic of Quadratic Forms* (2010), Lemma 21.6, and Weil, *Basic Number Theory*, Ch. V, Thm. 2:
* `latticeGluing`: every family $(M_p)_p$ of local lattices with $M_p = \mathbb{Z}_p^n$ for almost all $p$ is the
  family of localizations of a lattice $L = \gamma\mathbb{Z}^n$.

It then restates the D15–D16 results that assumed the input without it (`latAction'`, `diag_smul'`,
`orbit_eq_genus'`, `stabilizer_std'`, `dosetEquivClassesInGenus'`, `card_aut_eq'`, `thetaKernel_mul_mem'`).

*Proof (direct over $\mathbb{Z}$; no CRT).*
1. **One prime** (`exists_glue_one`): for a prime $p$ and $h \in \mathrm{GL}_n(\mathbb{Q}_p)$ there is
   $\gamma \in \mathrm{GL}_n(\mathbb{Q})$ with $\gamma\mathbb{Z}_p^n = h\mathbb{Z}_p^n$ and $\gamma\mathbb{Z}_q^n = \mathbb{Z}_q^n$
   for all $q \ne p$. Take $L = \{v \in \mathbb{Q}^n : v \in h\mathbb{Z}_p^n,\ v \in \mathbb{Z}_q^n\ (q \ne p)\}$. With
   $p^kh$, $p^kh^{-1}$ integral, $p^k\mathbb{Z}^n \subseteq L \subseteq p^{-k}\mathbb{Z}^n$, so $L = \gamma\mathbb{Z}^n$
   (`exists_latOf_of_bounds`, bases of submodules over a PID). Then $L_p = h\mathbb{Z}_p^n$: for $w \in h\mathbb{Z}_p^n$
   write $p^kw_i = a_i + p^{2k}t_i$ with $a_i \in \mathbb{Z}$, $t_i \in \mathbb{Z}_p$ (`exists_int_approx`); then
   $v = p^{-k}a \in L$ and $w - v = p^kt \in p^k\mathbb{Z}_p^n \subseteq L_p$.
2. **Finitely many primes** (`exists_glue_finset`), by induction on the finite set $S$ of primes where
   $M_p \ne \mathbb{Z}_p^n$: if $\gamma'$ glues the family with $M_p$ replaced by $\mathbb{Z}_p^n$, and $\delta$ glues
   $\gamma'^{-1}M_p$ at the single prime $p$, then $\gamma = \gamma'\delta$ glues $(M_q)_q$.

The same theorem over any number field is `Lattices.LocFamily.loc_glue`; this direct proof avoids the
bridge between `ℚ_[p]` and Mathlib's `adicCompletion ℚ v` and between the two lattice types.
-/
import QuadFormsKB.Literature.AWS.ThetaLift

open Matrix

namespace QuadFormsKB.AWS

variable {n : ℕ}

/-! ### p-adic integral vectors -/

section padicVec

variable {p : ℕ} [Fact p.Prime]

theorem IsIntVecP.add {u w : Fin n → ℚ_[p]} (hu : IsIntVecP p u) (hw : IsIntVecP p w) :
    IsIntVecP p (u + w) :=
  fun i => (Padic.nonarchimedean (u i) (w i)).trans (max_le (hu i) (hw i))

theorem IsIntVecP.neg {u : Fin n → ℚ_[p]} (hu : IsIntVecP p u) : IsIntVecP p (-u) :=
  fun i => by rw [Pi.neg_apply, norm_neg]; exact hu i

theorem IsIntVecP.sub {u w : Fin n → ℚ_[p]} (hu : IsIntVecP p u) (hw : IsIntVecP p w) :
    IsIntVecP p (u - w) := by
  rw [sub_eq_add_neg]; exact hu.add hw.neg

theorem IsIntVecP.smul {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) {u : Fin n → ℚ_[p]} (hu : IsIntVecP p u) :
    IsIntVecP p (c • u) :=
  fun i => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]; exact by nlinarith [norm_nonneg c, norm_nonneg (u i), hu i]

theorem isIntVecP_castP_of_isIntVec {v : Fin n → ℚ} (hv : IsIntVec v) : IsIntVecP p (castP p v) :=
  fun i => by
    obtain ⟨z, hz⟩ := hv i
    simp only [castP, hz, Rat.cast_intCast]
    exact Padic.norm_int_le_one z

/-- **$p^k A$ is integral for all large $k$**, for any $A \in M_n(\mathbb{Q}_p)$. -/
theorem eventually_isIntP_pow_smul (A : Matrix (Fin n) (Fin n) ℚ_[p]) :
    ∀ᶠ k : ℕ in Filter.atTop, IsIntP p ((p : ℚ_[p]) ^ k • A) := by
  refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
  have ht : Filter.Tendsto (fun k : ℕ => ‖(p : ℚ_[p])‖ ^ k * ‖A i j‖) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (Padic.norm_p_lt_one (p := p))).mul_const
      ‖A i j‖
  filter_upwards [ht.eventually (ge_mem_nhds one_pos)] with k hk
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  exact hk

/-- **Approximation by integers:** for $x \in \mathbb{Z}_p$ and $K \in \mathbb{N}$, $x = a + p^K t$ with $a \in \mathbb{Z}$ and
$t \in \mathbb{Z}_p$ (Mathlib's `PadicInt.appr`). -/
theorem exists_int_approx {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) (K : ℕ) :
    ∃ a : ℤ, ∃ t : ℚ_[p], ‖t‖ ≤ 1 ∧ x = a + (p : ℚ_[p]) ^ K * t := by
  set x' : ℤ_[p] := ⟨x, hx⟩
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec K x')
  refine ⟨(x'.appr K : ℤ), t, t.norm_le_one, ?_⟩
  have := congrArg (fun y : ℤ_[p] => (y : ℚ_[p])) ht
  simp only [PadicInt.coe_sub, PadicInt.coe_natCast, PadicInt.coe_mul, PadicInt.coe_pow] at this
  have hx' : (x' : ℚ_[p]) = x := rfl
  rw [hx'] at this
  push_cast
  linear_combination this

end padicVec

/-! ### Lattices sandwiched between $D\mathbb{Z}^n$ and $D^{-1}\mathbb{Z}^n$ are $\gamma\mathbb{Z}^n$ -/

/-- **A $\mathbb{Z}$-submodule with $D\mathbb{Z}^n \subseteq L \subseteq D^{-1}\mathbb{Z}^n$ ($D \ne 0$) is a lattice
$\gamma\mathbb{Z}^n$**, $\gamma \in \mathrm{GL}_n(\mathbb{Q})$ (Mathlib's bases of submodules over a PID,
`Submodule.basisOfPidOfLE`; cf. `Siegel.Kneser.exists_basis_of_le` for $D = p$). -/
theorem exists_latOf_of_bounds {D : ℕ} (hD : D ≠ 0) (L : Submodule ℤ (Fin n → ℚ))
    (h1 : ∀ v ∈ L, IsIntVec ((D : ℚ) • v))
    (h2 : ∀ z : Fin n → ℤ, ((D : ℚ) • fun i => (z i : ℚ)) ∈ L) :
    ∃ γ : GL (Fin n) ℚ, (L : Set (Fin n → ℚ)) = latOf γ := by
  classical
  have hDq : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  set e : Fin n → (Fin n → ℚ) := fun i => (1 / (D : ℚ)) • Pi.single i 1 with he
  have hli : LinearIndependent ℤ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, e, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)] at this
    simp only [ite_true, zsmul_eq_mul] at this
    have : (c i : ℚ) = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · simp [hDq] at h
    exact_mod_cast this
  let T := Submodule.span ℤ (Set.range e)
  let bT : Module.Basis (Fin n) ℤ T := Module.Basis.span hli
  have hLT : L ≤ T := by
    intro v hv
    choose z hz using h1 v hv
    have hv' : v = ∑ i, z i • e i := by
      ext j
      have := hz j
      simp only [Pi.smul_apply, smul_eq_mul] at this
      simp [e, Finset.sum_apply, Pi.single_apply, ← this]
      field_simp
    rw [hv']
    exact T.sum_mem fun i _ => T.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨k, bL⟩ := Submodule.basisOfPidOfLE hLT bT
  have : Module.Finite ℤ T := Module.Finite.of_basis bT
  have : Module.Finite ℤ L := Module.Finite.of_basis bL
  have hk1 : k ≤ n := by
    have hli' : LinearIndependent ℤ ((Submodule.inclusion hLT) ∘ bL) :=
      bL.linearIndependent.map' _ (Submodule.ker_inclusion _ _ hLT)
    have := hli'.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_eq_card_basis bT, Fintype.card_fin] at this
  have hk2 : n ≤ k := by
    let w : Fin n → L := fun i => ⟨_, h2 (Pi.single i 1)⟩
    have hliw : LinearIndependent ℤ w := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have := congrArg (fun x : L => (x : Fin n → ℚ) i) hc
      simp only [w, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Pi.single_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply] at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)] at this
      simp only [ite_true, Int.cast_one, mul_one, zsmul_eq_mul] at this
      have : (c i : ℚ) = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hDq
      exact_mod_cast this
    have := hliw.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_eq_card_basis bL, Fintype.card_fin] at this
  have hk : k = n := le_antisymm hk1 hk2
  subst hk
  let g : Matrix (Fin k) (Fin k) ℚ := Matrix.of fun i j => ((bL j : L) : Fin k → ℚ) i
  have hmv : ∀ c : Fin k → ℤ, g *ᵥ (fun i => (c i : ℚ)) = ∑ j, c j • ((bL j : L) : Fin k → ℚ) := by
    intro c; ext i
    simp only [mulVec, dotProduct, g, Matrix.of_apply, Finset.sum_apply, zsmul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hLg : ∀ x, x ∈ L ↔ ∃ c : Fin k → ℤ, x = g *ᵥ (fun i => (c i : ℚ)) := by
    intro x
    constructor
    · intro hx
      refine ⟨fun j => bL.repr ⟨x, hx⟩ j, ?_⟩
      rw [hmv]
      have := congrArg (fun y : L => (y : Fin k → ℚ)) (bL.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    · rintro ⟨c, rfl⟩
      rw [hmv]
      exact L.sum_mem fun j _ => L.smul_mem _ (bL j).2
  -- `g C = D • 1` for an integer matrix `C`, so `det g ≠ 0`
  have hC : ∀ i, ∃ c : Fin k → ℤ,
      ((D : ℚ) • fun r => ((Pi.single i (1 : ℤ) : Fin k → ℤ) r : ℚ)) = g *ᵥ (fun r => (c r : ℚ)) :=
    fun i => (hLg _).mp (h2 _)
  choose C hC using hC
  let Cm : Matrix (Fin k) (Fin k) ℚ := Matrix.of fun r i => (C i r : ℚ)
  have hgC : g * Cm = (D : ℚ) • (1 : Matrix (Fin k) (Fin k) ℚ) := by
    ext r i
    have h1 := congrFun (hC i) r
    have h2 : (g * Cm) r i = (g *ᵥ fun s => (C i s : ℚ)) r := by
      simp only [mul_apply, mulVec, dotProduct, Cm, of_apply]
    rw [h2, ← h1]
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  have hdet : g.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hgC
    rw [det_mul, h0, zero_mul, det_smul, det_one, mul_one, Fintype.card_fin] at this
    exact pow_ne_zero _ hDq this.symm
  refine ⟨GeneralLinearGroup.mkOfDetNeZero g hdet, ?_⟩
  set γ := GeneralLinearGroup.mkOfDetNeZero g hdet
  have hγ : γ.val = g := rfl
  ext x
  simp only [SetLike.mem_coe, latOf, Set.mem_ofPred_eq]
  rw [hLg]
  constructor
  · rintro ⟨c, rfl⟩ i
    refine ⟨c i, ?_⟩
    rw [← hγ, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  · intro hx
    choose c hc using hx
    refine ⟨c, ?_⟩
    have : (fun i => (c i : ℚ)) = γ⁻¹.val *ᵥ x := funext fun i => (hc i).symm
    rw [this, ← hγ, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

/-! ### Gluing at one prime -/

/-- For distinct primes $q \ne p$, $\|p^k\|_q = 1$. -/
theorem norm_pow_prime_eq_one {p q : PrimeIdx} (hq : q ≠ p) (k : ℕ) :
    ‖(((p : ℕ) ^ k : ℕ) : ℚ_[(q : ℕ)])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  refine Nat.Coprime.pow_right _ ?_
  exact (Nat.coprime_primes q.2 p.2).mpr (fun h => hq (Subtype.ext h))

theorem castP_add (p : ℕ) [Fact p.Prime] (u v : Fin n → ℚ) :
    castP p (u + v) = castP p u + castP p v := by
  funext i; simp [castP]

theorem castP_smul (p : ℕ) [Fact p.Prime] (a : ℚ) (v : Fin n → ℚ) :
    castP p (a • v) = (a : ℚ_[p]) • castP p v := by
  funext i; simp [castP]

theorem castP_mulVec (p : ℕ) [Fact p.Prime] (g : GL (Fin n) ℚ) (v : Fin n → ℚ) :
    castP p (g.val *ᵥ v) = (glP p g).val *ᵥ castP p v :=
  (mulVec_cast p g.val v).symm

/-- **Gluing at one prime** (the key step of Lemma 4.5.1): for a prime $p$ and $h \in \mathrm{GL}_n(\mathbb{Q}_p)$ there
is $\gamma \in \mathrm{GL}_n(\mathbb{Q})$ with $\gamma\mathbb{Z}_p^n = h\mathbb{Z}_p^n$ and $\gamma\mathbb{Z}_q^n = \mathbb{Z}_q^n$ for
every prime $q \ne p$. -/
@[kb "hanke2011aws" "§4.5, Lemma 4.5.1, p. 61"]
theorem exists_glue_one (p : PrimeIdx) (h : GL (Fin n) ℚ_[(p : ℕ)]) :
    ∃ γ : GL (Fin n) ℚ, latOfP (p : ℕ) (glP (p : ℕ) γ) = latOfP (p : ℕ) h ∧
      ∀ q : PrimeIdx, q ≠ p → latOfP (q : ℕ) (glP (q : ℕ) γ) = latOfP (q : ℕ) 1 := by
  classical
  obtain ⟨k, hk1, hk2⟩ :=
    ((eventually_isIntP_pow_smul h.val).and (eventually_isIntP_pow_smul h⁻¹.val)).exists
  set c : ℚ_[(p : ℕ)] := ((p : ℕ) : ℚ_[(p : ℕ)]) ^ k with hc
  set D : ℕ := (p : ℕ) ^ k with hDdef
  have hD : D ≠ 0 := pow_ne_zero _ p.2.ne_zero
  have hcD : ((D : ℚ) : ℚ_[(p : ℕ)]) = c := by simp [hDdef, hc]
  have hc0 : c ≠ 0 := pow_ne_zero _ (by exact_mod_cast p.2.ne_zero)
  have hcn : ‖c‖ ≤ 1 := by rw [hc, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (Padic.norm_p_lt_one).le
  -- the two bounds of `h ℤ_p^n`
  have hA : ∀ w : Fin n → ℚ_[(p : ℕ)], IsIntVecP (p : ℕ) (h⁻¹.val *ᵥ w) → IsIntVecP (p : ℕ) (c • w) := by
    intro w hw
    have : c • w = (c • h.val) *ᵥ (h⁻¹.val *ᵥ w) := by
      rw [smul_mulVec, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [this]; exact hk1.mulVec hw
  have hB : ∀ u : Fin n → ℚ_[(p : ℕ)], IsIntVecP (p : ℕ) u → IsIntVecP (p : ℕ) (h⁻¹.val *ᵥ (c • u)) := by
    intro u hu
    rw [mulVec_smul, ← smul_mulVec]; exact hk2.mulVec hu
  have hDq : ∀ q : PrimeIdx, q ≠ p → ‖((D : ℚ) : ℚ_[(q : ℕ)])‖ = 1 := by
    intro q hq
    have := norm_pow_prime_eq_one hq k
    simpa [hDdef] using this
  have hDq' : ∀ q : PrimeIdx, ‖((D : ℚ) : ℚ_[(q : ℕ)])‖ ≤ 1 := by
    intro q
    have := Padic.norm_int_le_one (p := (q : ℕ)) (D : ℤ)
    simpa using this
  -- the global lattice
  let L : Submodule ℤ (Fin n → ℚ) :=
    { carrier := {v | IsIntVecP (p : ℕ) (h⁻¹.val *ᵥ castP (p : ℕ) v) ∧
        ∀ q : PrimeIdx, q ≠ p → IsIntVecP (q : ℕ) (castP (q : ℕ) v)}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, fun q hq => ?_⟩
        · rw [castP_add, mulVec_add]; exact ha1.add hb1
        · rw [castP_add]; exact (ha2 q hq).add (hb2 q hq)
      zero_mem' := by
        have e : ∀ (r : ℕ) [Fact r.Prime], castP r (0 : Fin n → ℚ) = 0 :=
          fun r _ => by funext i; simp [castP]
        refine ⟨?_, fun q _ => ?_⟩
        · rw [e, mulVec_zero]; intro i; simp
        · rw [e]; intro i; simp
      smul_mem' := by
        rintro a v ⟨hv1, hv2⟩
        have e : ∀ (r : ℕ) [Fact r.Prime], castP r (a • v) = ((a : ℚ) : ℚ_[r]) • castP r v := by
          intro r _; rw [← castP_smul, Int.cast_smul_eq_zsmul]
        have hn : ∀ (r : ℕ) [Fact r.Prime], ‖((a : ℚ) : ℚ_[r])‖ ≤ 1 := by
          intro r _; simpa using Padic.norm_int_le_one (p := r) a
        refine ⟨?_, fun q hq => ?_⟩
        · rw [e, mulVec_smul]; exact hv1.smul (hn _)
        · rw [e]; exact (hv2 q hq).smul (hn _) }
  have hmemL : ∀ v, v ∈ L ↔ IsIntVecP (p : ℕ) (h⁻¹.val *ᵥ castP (p : ℕ) v) ∧
      ∀ q : PrimeIdx, q ≠ p → IsIntVecP (q : ℕ) (castP (q : ℕ) v) := fun _ => Iff.rfl
  have h1 : ∀ v ∈ L, IsIntVec ((D : ℚ) • v) := by
    intro v hv i
    rw [rat_isInt_iff]
    intro q
    rcases eq_or_ne q p with rfl | hq
    · have := hA _ hv.1 i
      simpa [castP, hcD] using this
    · have := (hv.2 q hq).smul (hDq' q) i
      simpa [castP] using this
  have h2 : ∀ z : Fin n → ℤ, ((D : ℚ) • fun i => (z i : ℚ)) ∈ L := by
    intro z
    have hz : ∀ (r : ℕ) [Fact r.Prime], IsIntVecP r (castP r fun i => (z i : ℚ)) :=
      fun r _ => isIntVecP_castP_of_isIntVec fun i => ⟨z i, rfl⟩
    refine ⟨?_, fun q hq => ?_⟩
    · rw [castP_smul, hcD]; exact hB _ (hz _)
    · rw [castP_smul]; exact (hz _).smul (hDq' q)
  obtain ⟨γ, hγ⟩ := exists_latOf_of_bounds hD L h1 h2
  have hγL : ∀ v, v ∈ L ↔ IsIntVec (γ⁻¹.val *ᵥ v) := fun v => by
    rw [← SetLike.mem_coe, hγ]; rfl
  -- columns of `γ` and of `D γ⁻¹`
  have hcol : ∀ j, γ.val *ᵥ Pi.single j 1 ∈ L := by
    intro j
    rw [hγL, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    intro i; by_cases hij : i = j
    · exact ⟨1, by subst hij; simp⟩
    · exact ⟨0, by simp [hij]⟩
  have hinvcol : ∀ i j, ∃ z : ℤ, (D : ℚ) * γ⁻¹.val i j = z := by
    intro i j
    have := (hγL _).mp (h2 (Pi.single j 1)) i
    obtain ⟨z, hz⟩ := this
    refine ⟨z, ?_⟩
    rw [← hz, mulVec_smul]
    have e : (fun r => ((Pi.single j (1 : ℤ) : Fin n → ℤ) r : ℚ)) = Pi.single j 1 := by
      funext r; by_cases hr : r = j
      · subst hr; simp
      · simp [hr]
    rw [e, mulVec_single]; simp
  have hglP : ∀ (r : ℕ) [Fact r.Prime] (i j : Fin n),
      (glP r γ).val i j = ((γ.val *ᵥ Pi.single j 1) i : ℚ_[r]) := by
    intro r _ i j; simp [glP, mulVec_single]
  refine ⟨γ, ?_, fun q hq => ?_⟩
  · -- the localization at `p`
    have hI1 : IsIntP (p : ℕ) (h⁻¹.val * (glP (p : ℕ) γ).val) := by
      intro i j
      have := (hcol j).1 i
      have e : castP (p : ℕ) (Pi.single j (1 : ℚ) : Fin n → ℚ) = Pi.single j 1 := by
        funext r; by_cases hr : r = j
        · subst hr; simp [castP]
        · simp [castP, hr]
      rw [castP_mulVec, mulVec_mulVec, e, mulVec_single] at this
      simpa using this
    have hI2 : IsIntP (p : ℕ) (c • (glP (p : ℕ) γ)⁻¹.val) := by
      intro i j
      obtain ⟨z, hz⟩ := hinvcol i j
      rw [Matrix.smul_apply, glP_inv_val, Matrix.map_apply, smul_eq_mul, ← hcD]
      have : ((D : ℚ) : ℚ_[(p : ℕ)]) * (algebraMap ℚ ℚ_[(p : ℕ)] (γ⁻¹.val i j)) = (z : ℚ_[(p : ℕ)]) := by
        rw [eq_ratCast, ← Rat.cast_mul, hz, Rat.cast_intCast]
      rw [this]; exact Padic.norm_int_le_one z
    ext w
    simp only [latOfP, Set.mem_ofPred_eq]
    constructor
    · intro hw
      have : h⁻¹.val *ᵥ w = (h⁻¹.val * (glP (p : ℕ) γ).val) *ᵥ ((glP (p : ℕ) γ)⁻¹.val *ᵥ w) := by
        rw [mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]
      rw [this]; exact hI1.mulVec hw
    · intro hw
      have hcw := hA w hw
      choose a t ht hdec using fun i => exists_int_approx (hcw i) (k + k)
      set v : Fin n → ℚ := fun i => (a i : ℚ) / D
      have hwv : w = castP (p : ℕ) v + c • t := by
        funext i
        have := hdec i
        simp only [Pi.smul_apply, smul_eq_mul] at this
        simp only [castP, v, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_div, Rat.cast_intCast]
        rw [show (((D : ℚ)) : ℚ_[(p : ℕ)]) = c from hcD] at *
        rw [pow_add, ← hc] at this
        field_simp
        linear_combination this
      have hvL : v ∈ L := by
        refine ⟨?_, fun q hq i => ?_⟩
        · have e : castP (p : ℕ) v = w - c • t := by rw [hwv]; abel
          rw [e, mulVec_sub]
          exact hw.sub (hB t ht)
        · simp only [castP, v, Rat.cast_div, Rat.cast_intCast, norm_div, hDq q hq, div_one]
          exact Padic.norm_int_le_one _
      have e : (glP (p : ℕ) γ)⁻¹.val *ᵥ w =
          castP (p : ℕ) (γ⁻¹.val *ᵥ v) + (c • (glP (p : ℕ) γ)⁻¹.val) *ᵥ t := by
        rw [hwv, mulVec_add, smul_mulVec, ← mulVec_smul, glP_inv_val]
        congr 1
        exact mulVec_cast _ _ _
      rw [e]
      exact (isIntVecP_castP_of_isIntVec ((hγL v).mp hvL)).add (hI2.mulVec ht)
  · -- the localizations at `q ≠ p` are standard
    apply latOfP_eq_std
    · intro i j
      rw [hglP]
      exact (hcol j).2 q hq i
    · intro i j
      obtain ⟨z, hz⟩ := hinvcol i j
      rw [glP_inv_val, Matrix.map_apply, eq_ratCast]
      have hn : ‖((D : ℚ) : ℚ_[(q : ℕ)]) * ((γ⁻¹.val i j : ℚ) : ℚ_[(q : ℕ)])‖ ≤ 1 := by
        rw [← Rat.cast_mul, hz, Rat.cast_intCast]; exact Padic.norm_int_le_one z
      rwa [norm_mul, hDq q hq, one_mul] at hn

/-! ### Gluing at finitely many primes -/

/-- If $m\mathbb{Z}_p^n = m'\mathbb{Z}_p^n$ then $gm\mathbb{Z}_p^n = gm'\mathbb{Z}_p^n$. -/
theorem latOfP_mul_congr {p : ℕ} [Fact p.Prime] (g : GL (Fin n) ℚ_[p]) {m m' : GL (Fin n) ℚ_[p]}
    (h : latOfP p m = latOfP p m') : latOfP p (g * m) = latOfP p (g * m') := by
  rw [← locAct_latOfP, ← locAct_latOfP]
  exact congrArg (fun M => (locAct g M).1)
    (LocLat.ext h : (⟨latOfP p m, m, rfl⟩ : LocLat p n) = ⟨latOfP p m', m', rfl⟩)

/-- **Gluing for families standard outside a finite set** $S$ of primes, by induction on $S$. -/
theorem exists_glue_finset (S : Finset PrimeIdx) :
    ∀ M : (p : PrimeIdx) → LocLat (p : ℕ) n, (∀ p, p ∉ S → M p = stdLoc (p : ℕ)) →
      ∃ γ : GL (Fin n) ℚ, ∀ p : PrimeIdx, latOfP (p : ℕ) (glP (p : ℕ) γ) = (M p).1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro M hM
    refine ⟨1, fun p => ?_⟩
    rw [hM p (Finset.notMem_empty p), stdLoc]
    congr 1; simp [glP]
  | insert p S hpS ih =>
    intro M hM
    let M' : (q : PrimeIdx) → LocLat (q : ℕ) n := Function.update M p (stdLoc (p : ℕ))
    obtain ⟨γ', hγ'⟩ := ih M' fun q hq => by
      by_cases hqp : q = p
      · subst hqp; simp [M']
      · simp only [M', Function.update_of_ne hqp]
        exact hM q (by simp [hqp, hq])
    obtain ⟨m, hm⟩ := (M p).2
    obtain ⟨δ, hδp, hδq⟩ := exists_glue_one p ((glP (p : ℕ) γ')⁻¹ * m)
    refine ⟨γ' * δ, fun q => ?_⟩
    have hmul : glP (q : ℕ) (γ' * δ) = glP (q : ℕ) γ' * glP (q : ℕ) δ := map_mul _ _ _
    rw [hmul]
    rcases eq_or_ne q p with rfl | hq
    · rw [latOfP_mul_congr _ hδp, mul_inv_cancel_left, hm]
    · rw [latOfP_mul_congr _ (hδq q hq), mul_one, hγ' q]
      simp [M', Function.update_of_ne hq]

/-! ### The gluing theorem -/

/-- **Lemma 4.5.1, existence half (proved): gluing of lattices over $\mathbb{Q}$.** Every family $(M_p)_p$ of local
lattices $M_p \subset \mathbb{Q}_p^n$ with $M_p = \mathbb{Z}_p^n$ for all but finitely many primes $p$ is the family
of localizations $(L_p)_p$ of a lattice $L = \gamma\mathbb{Z}^n \subset \mathbb{Q}^n$; with `loc_injective`, $L$ is
unique. This discharges the input `LatticeGluing n` (cited in the notes from Shimura, *Arithmetic of Quadratic
Forms* (2010), Lemma 21.6, pp. 102–103, and Weil, *Basic Number Theory*, Ch. V, Thm. 2, p. 84). Over a number
field the same statement is `Lattices.LocFamily.loc_glue`. -/
@[kb "hanke2011aws" "§4.5, Lemma 4.5.1, p. 61"]
theorem latticeGluing (n : ℕ) : LatticeGluing n := by
  intro M hM
  have hfin : {p : PrimeIdx | ¬ M p = stdLoc (p : ℕ)}.Finite := Filter.eventually_cofinite.mp hM
  obtain ⟨γ, hγ⟩ := exists_glue_finset hfin.toFinset M fun p hp => by
    by_contra h; exact hp ((Set.Finite.mem_toFinset _).mpr h)
  refine ⟨⟨latOf γ, γ, rfl⟩, fun p => LocLat.ext ?_⟩
  rw [loc_eq_of _ _ rfl, hγ]

/-! ### Unconditional versions of D15–D16 and D20 -/

variable (H : Matrix (Fin n) (Fin n) ℚ)

/-- **The action of $O(V_\mathbb{A})$ on lattices** (notes, pp. 61–62), unconditional: `latAction` with the
proved gluing `latticeGluing`. -/
@[instance_reducible]
noncomputable def latAction' : MulAction (OA H) (Lat n) := latAction H (latticeGluing n)

/-- **A rational $\gamma \in O(V)$ acts by $L \mapsto \gamma L$** (notes, p. 62), unconditional form of
`diag_smul`. -/
@[kb "hanke2011aws" "§4.5, p. 62"]
theorem diag_smul' (γ : orthGroup H ℚ) (L : Lat n) :
    latSMul H (latticeGluing n) (diag H γ) L = latImage (γ : GL (Fin n) ℚ) L :=
  diag_smul H (latticeGluing n) γ L

/-- **Lemma 4.5.2 (p. 62), unconditional:** the $O(V_\mathbb{A})$-orbit of a lattice $L$ is the genus of $L$
(`orbit_eq_genus` with the proved gluing `latticeGluing`). -/
@[kb "hanke2011aws" "§4.5, Lemma 4.5.2, p. 62"]
theorem orbit_eq_genus' (L : Lat n) :
    @MulAction.orbit (OA H) (Lat n) (latAction' H).toSMul L = latGenus H L :=
  orbit_eq_genus H (latticeGluing n) L

/-- **$\mathrm{Stab}_\mathbb{A}(\mathbb{Z}^n) = K_\mathbb{A}$** (p. 62), unconditional form of `stabilizer_std`. -/
@[kb "hanke2011aws" "§4.5, p. 62"]
theorem stabilizer_std' :
    @MulAction.stabilizer (OA H) (Lat n) _ (latAction' H) stdLat = KA H :=
  stabilizer_std H (latticeGluing n)

/-- **D16 (p. 62), unconditional:** $O(V)\backslash O(V_\mathbb{A})/K_\mathbb{A} \simeq$ the classes in
$\mathrm{Gen}(\mathbb{Z}^n)$ (`dosetEquivClassesInGenus` with the proved gluing `latticeGluing`). -/
noncomputable def dosetEquivClassesInGenus' :=
  dosetEquivClassesInGenus H (latticeGluing n)

/-- **(4.11), p. 64, unconditional:** $|O(V) \cap \alpha K_\mathbb{A}\alpha^{-1}| = |\mathrm{Aut}(\alpha\mathbb{Z}^n)|$
(`card_aut_eq` with the proved gluing `latticeGluing`). -/
@[kb "hanke2011aws" "§4.6, (4.11), p. 64"]
theorem card_aut_eq' (α : OA H) :
    Nat.card (ratPoints H ⊓ conjSub α (KA H) : Subgroup (OA H)) =
      Nat.card (autLat H (latSMul H (latticeGluing n) α stdLat)) :=
  card_aut_eq H (latticeGluing n) α

open scoped Classical in
/-- **D20: (4.18)–(4.22), p. 64, unconditional:** for $\alpha \in O(V_\mathbb{A})$ with $\alpha_\infty = 1$ and
$k \in K_\mathbb{A}$, $\theta(g_{\infty,z}, \alpha k) = \sum_{\vec v \in \alpha\mathbb{Z}^n} y^{n/4}e^{2\pi i z Q(\vec v)}$
(`thetaKernel_mul_mem` with the proved gluing `latticeGluing`). -/
@[kb "hanke2011aws" "§4.6, (4.18)-(4.22), p. 64"]
theorem thetaKernel_mul_mem' (Q : QuadForm ℚ n) (z : UpperHalfPlane) (α : OA Q.hessian) (hα : α.1 = 1)
    {k : OA Q.hessian} (hk : k ∈ KA Q.hessian) :
    thetaKernel Q z (α * k) = ∑' v : Fin n → ℚ,
      if v ∈ (latSMul Q.hessian (latticeGluing n) α stdLat).1 then
        ((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) * (Q.evalIn ℚ v : ℂ))
      else 0 :=
  thetaKernel_mul_mem Q (latticeGluing n) z α hα hk

/-- **The theta-lift inputs with the gluing field discharged:** `AWSInputs Q` from its two remaining
fields, the finiteness of the class set and of the groups $O(V) \cap \alpha K_\mathbb{A}\alpha^{-1}$
(notes, §4.6, p. 64); the field `gluing` is `latticeGluing`. -/
theorem AWSInputs.ofFinite (Q : QuadForm ℚ n)
    (finite_classes : Finite (DoubleCoset.Quotient (ratPoints Q.hessian : Set (OA Q.hessian)) (KA Q.hessian)))
    (finite_aut : ∀ α : OA Q.hessian,
      Finite (ratPoints Q.hessian ⊓ conjSub α (KA Q.hessian) : Subgroup _)) :
    AWSInputs Q :=
  ⟨latticeGluing n, finite_classes, finite_aut⟩

end QuadFormsKB.AWS
