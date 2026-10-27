/-
# Cassels, Chapter 11, Theorem 6.2, Corollary: the spinor genera along a chain

**Layer:** integer forms $f$ = `QuadForm ℤ n` and Cassels' chains of Theorem 6.1 (`Ch11Sec6.lean`); the space
$V = (\mathbb Q^n, f_1)$ with $\Lambda = \mathbb Z^n$; the lattice of a form $f_2$ rationally equivalent to $f_1$ is
$\Gamma = g\mathbb Z^n$ for any $g \in \mathrm{SL}_n(\mathbb Q)$ with $f_2(x) = f_1(gx)$ (its proper class, hence its
spinor genus, does not depend on $g$). As in Theorem 4.1 (`Ch11Sec4Thm.lean`) the action $g(W)\mathcal S$ of $G$ is
unfolded: $\mathcal S_\Gamma = g(W)\mathcal S_\Lambda$ means that $\Gamma$ is in the spinor genus of $\alpha\Lambda$
for $\alpha \in O(V)(\mathbb A_f)$ with $\alpha_p \in O^+(V_p)$, $\theta(\alpha_p) = W(\mathbb Q_p^\times)^2$ for
$p \in P$, $\alpha_p = 1$ for $p \notin P$, where $P$ is Cassels' $P^*$ for $\Lambda$.

**Proves** Cassels' Theorem 6.2, Corollary (p. 226) (`sameProperSpinorGenus_of_chain`): for $n \ge 3$ and a chain
$f_1 = g_0, \dots, g_V = f_2$ whose steps (ii) use primes $p \notin P$, with $W$ the product of these primes,
$\mathcal S_{f_2} = g(W)\mathcal S_{f_1}$. *Proof* (Cassels: "follows at once from Theorem 4.1"): along the chain the
lattices $\Gamma_v = T_v\mathbb Z^n$ ($g_v(x) = f_1(T_vx)$) change by proper equivalences (steps (i)) and by
$I(\Gamma_{v+1}, \Gamma_v) = p$ (steps (ii)); apply Theorem 4.1 at each step (ii).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec6Genus
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ}

open Siegel.Kneser in
theorem mem_intVec_Q (x : Fin n → ℚ) :
    x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ ∃ z : Fin n → ℤ, x = cv z := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := mem_intVec_iff_exists.mp h
    exact ⟨fun i => Rat.ringOfIntegersEquiv (a i), by
      ext i; simp [cv, intCoe, Rat.ringOfIntegersEquiv_apply_coe]⟩
  · rintro ⟨z, rfl⟩
    exact mem_intVec_iff_exists.mpr ⟨fun i => (z i : 𝓞 ℚ), by ext i; simp [cv, intCoe]⟩

open Siegel.Kneser in
theorem mem_latOf_Q (T : GL (Fin n) ℚ) (x : Fin n → ℚ) :
    x ∈ latOf T ↔ ∃ z : Fin n → ℤ, x = T.val *ᵥ cv z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (mem_intVec_Q y).mp hy
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact mem_latOf_cv T z

theorem latOf_mul_int (T : GL (Fin n) ℚ) (U : Matrix (Fin n) (Fin n) ℤ) (hU : U.det = 1)
    (V : GL (Fin n) ℚ) (hV : V.val = U.map (Int.castRingHom ℚ)) : latOf (T * V) = latOf T := by
  ext x
  rw [mem_latOf_Q, mem_latOf_Q]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨U *ᵥ z, ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec, hV, cast_mulVec_cv]
  · rintro ⟨z, rfl⟩
    refine ⟨U.adjugate *ᵥ z, ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec, hV, cast_mulVec_cv, mulVec_mulVec, Matrix.mul_adjugate, hU,
      one_smul, one_mulVec]

theorem casselsI_latOf_subst (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime) (T S : GL (Fin n) ℚ)
    (hS : S.val = casselsSubstDiag n p) :
    casselsI (⟨latOf (T * S), latOf_isLattice _⟩ : Lat ℚ n) ⟨latOf T, latOf_isLattice _⟩ = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set X : GL (Fin n) ℚ := T * S with hX
  let Φ : (Fin n → ℤ) →+ (Fin n → ℚ) :=
    AddMonoidHom.mk' (fun z => X.val *ᵥ Siegel.Kneser.cv z)
      (fun a b => by rw [Siegel.Kneser.cv_add, mulVec_add])
  have hXinj : Function.Injective fun y : Fin n → ℚ => X.val *ᵥ y :=
    Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit X)
  have hTinj : Function.Injective fun y : Fin n → ℚ => T.val *ᵥ y :=
    Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit T)
  have hΦinj : Function.Injective Φ := fun a b h =>
    Siegel.Kneser.cv_injective (hXinj h)
  have hrange : Φ.range = (latOf X).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_range]
    show (∃ z, X.val *ᵥ Siegel.Kneser.cv z = x) ↔ x ∈ latOf X
    rw [mem_latOf_Q]
    constructor <;> rintro ⟨z, hz⟩ <;> exact ⟨z, hz.symm⟩
  let j0 : Fin n := ⟨0, by omega⟩
  let jl : Fin n := ⟨n - 1, by omega⟩
  have hj : j0 ≠ jl := fun h => by have := congrArg Fin.val h; simp [j0, jl] at this; omega
  have key : ∀ z : Fin n → ℤ, X.val *ᵥ Siegel.Kneser.cv z ∈ latOf T ↔ (p : ℤ) ∣ z jl := by
    intro z
    have hXz : X.val *ᵥ Siegel.Kneser.cv z = T.val *ᵥ casselsSubst p (Siegel.Kneser.cv z) := by
      rw [hX, Units.val_mul, ← mulVec_mulVec, hS, casselsSubst_eq]
    rw [hXz, mem_latOf_Q]
    constructor
    · rintro ⟨w, hw⟩
      have h1 := hTinj hw
      have h2 := congrFun h1 jl
      have e0 : n - 1 ≠ 0 := by omega
      simp [casselsSubst, jl, e0] at h2
      refine ⟨w jl, ?_⟩
      have : (z jl : ℚ) = p * w jl := by field_simp at h2; linarith
      exact_mod_cast this
    · rintro ⟨m, hm⟩
      refine ⟨fun i => if i.1 = 0 then p * z i else if i.1 = n - 1 then m else z i, ?_⟩
      congr 1
      funext i
      simp only [casselsSubst, Siegel.Kneser.cv_apply]
      by_cases h0 : i.1 = 0
      · simp [h0]
      · by_cases hl : i.1 = n - 1
        · have : i = jl := Fin.ext hl
          subst this
          simp [jl, hm, hp0]
        · simp [h0, hl]
  have hH : ∀ z, z ∈ ((latOf X ⊓ latOf T).toAddSubgroup.comap Φ) ↔ (p : ℤ) ∣ z jl := by
    intro z
    rw [AddSubgroup.mem_comap]
    show X.val *ᵥ Siegel.Kneser.cv z ∈ latOf X ⊓ latOf T ↔ _
    rw [Submodule.mem_inf, key]
    exact ⟨fun h => h.2, fun h => ⟨(mem_latOf_Q X _).mpr ⟨z, rfl⟩, h⟩⟩
  unfold casselsI
  show ((latOf X ⊓ latOf T).toAddSubgroup).relIndex (latOf X).toAddSubgroup = p
  have hK : (latOf X ⊓ latOf T).toAddSubgroup =
      ((latOf X ⊓ latOf T).toAddSubgroup.comap Φ).map Φ := by
    rw [AddSubgroup.map_comap_eq, hrange]
    exact (inf_of_le_right (fun x hx => hx.1)).symm
  have hL : (latOf X).toAddSubgroup = (⊤ : AddSubgroup (Fin n → ℤ)).map Φ := by
    rw [← AddMonoidHom.range_eq_map, hrange]
  rw [hL, hK, AddSubgroup.relIndex_map_map_of_injective _ _ hΦinj, AddSubgroup.relIndex_top_right]
  let f : (Fin n → ℤ) →+ ZMod p :=
    (Int.castAddHom (ZMod p)).comp (Pi.evalAddMonoidHom (fun _ => ℤ) jl)
  have hker : ((latOf X ⊓ latOf T).toAddSubgroup.comap Φ) = f.ker := by
    ext z
    rw [hH, AddMonoidHom.mem_ker]
    show _ ↔ ((z jl : ℤ) : ZMod p) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨Pi.single jl (a.val : ℤ), ?_⟩
    simp [f]
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top]
  simp

theorem not_dvd_two_det {gs0 : QuadForm ℤ n} {P : Finset (HeightOneSpectrum (𝓞 ℚ))}
    (hP2 : ∀ v, (2 : 𝓞 ℚ) ∈ v.asIdeal → v ∈ P)
    (hPunim : ∀ v, v ∉ P →
      (∀ x ∈ loc v (stdLat : Lat ℚ n).1,
        Valued.v ((gs0.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧
      ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v (stdLat : Lat ℚ n).1 = locAct v γ (std v) ∧
        Valued.v (locGram (gs0.map (Int.castRingHom ℚ)) v γ).det = 1)
    {q : ℕ} (hq : q.Prime) (hqP : ∀ w ∈ P, Rat.HeightOneSpectrum.natGenerator w ≠ q) :
    ¬ (q : ℤ) ∣ 2 * gs0.hessian.det := by
  obtain ⟨vq, hvq⟩ := exists_place_natGen hq
  have hvqP : vq ∉ P := fun h => hqP vq h hvq
  obtain ⟨-, γ, hγ, hd⟩ := hPunim vq hvqP
  have hn : ‖γ.val.det‖ = ‖(1 : GL (Fin n) (vq.adicCompletion ℚ)).val.det‖ :=
    norm_det_eq_of_locAct_std_eq vq γ 1 (by rw [locAct_one, ← hγ]; exact loc_intVec vq)
  have hv := valued_eq_of_norm_eq vq (Matrix.isUnits_det_units γ).ne_zero (by simp) hn
  have e := (locGram_one_int_det vq gs0).symm.trans (locGram_det (Q := gs0.map (Int.castRingHom ℚ)) (v := vq) 1)
  simp only [Units.val_one, det_one, one_pow, one_mul] at e
  rw [locGram_det, map_mul, map_pow, hv] at hd
  simp only [Units.val_one, det_one, map_one, one_pow, one_mul] at hd
  rw [← e] at hd
  intro hdvd
  rcases (Nat.prime_iff_prime_int.mp hq).dvd_or_dvd hdvd with h2 | hdd
  · have h2' : q ∣ 2 := by exact_mod_cast h2
    have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2'
    exact hvqP (hP2 vq ((two_mem_iff_natGenerator vq).mpr (hvq.trans this)))
  · have := (valued_intCast_le_iff vq gs0.hessian.det 1).mpr (by rw [hvq]; simpa using hdd)
    rw [hd] at this
    have h1 : (WithZero.exp (-(1 : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by simp
    exact absurd this (not_le.mpr h1)

theorem exists_gl_of_det (M : Matrix (Fin n) (Fin n) ℚ) (h : M.det = 1) :
    ∃ G : GL (Fin n) ℚ, G.val = M :=
  ⟨Matrix.nonsingInvUnit M (by rw [h]; exact isUnit_one), rfl⟩

/-- **Cassels, Theorem 6.2, Corollary** (Ch. 11, p. 226): *suppose that $n \ge 3$. Let $\mathcal S_j$ be the spinor
genus of $f_j$ ($j = 1, 2$) and let $W$ be the product of the primes occurring in the substitutions of type (ii). Then
$\mathcal S_2 = g_W\mathcal S_1$ in the notation of Theorem 3.1, where $g_W = g(W)$ is the image of $W$ in $G$ under the
map (4.5).* Here the chain is $g_0 = f_1, \dots, g_V = f_2$ with steps of type (ii) exactly at $v \in S$, with prime
`pr v` $\notin P$; $W = \prod_{v \in S}$ `pr v`; $\Gamma = g\mathbb Z^n$ is the lattice of $f_2$ in $(\mathbb Q^n, f_1)$
and $g(W)\mathcal S_1$ is unfolded as in the module docstring. -/
@[kb "cassels1978" "Ch. 11, Thm. 6.2, Cor., p. 226 (g(W)𝒮 unfolded via (3.32))"]
theorem sameProperSpinorGenus_of_chain (hn : 3 ≤ n) (V : ℕ) (gs : Fin (V + 1) → QuadForm ℤ n)
    (hint : ∀ v, IsClassicallyIntegral (gs v)) (hdet : ∀ v, (gs v).hessian.det = (gs 0).hessian.det)
    (hd0 : (gs 0).hessian.det ≠ 0)
    (S : Finset (Fin V)) (pr : Fin V → ℕ)
    (hi : ∀ v, v ∉ S → ∃ U : Matrix (Fin n) (Fin n) ℤ, U.det = 1 ∧
      ∀ x, (gs v.succ).eval x = (gs v.castSucc).eval (U *ᵥ x))
    (hii : ∀ v ∈ S, (pr v).Prime ∧ ∀ x : Fin n → ℚ, ((gs v.succ).map (Int.castRingHom ℚ)).evalIn ℚ x =
      ((gs v.castSucc).map (Int.castRingHom ℚ)).evalIn ℚ (casselsSubst (pr v) x))
    (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (hP2 : ∀ v, (2 : 𝓞 ℚ) ∈ v.asIdeal → v ∈ P)
    (hPunim : ∀ v, v ∉ P →
      (∀ x ∈ loc v (stdLat : Lat ℚ n).1,
        Valued.v (((gs 0).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧
      ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v (stdLat : Lat ℚ n).1 = locAct v γ (std v) ∧
        Valued.v (locGram ((gs 0).map (Int.castRingHom ℚ)) v γ).det = 1)
    (hprP : ∀ v ∈ S, ∀ w ∈ P, Rat.HeightOneSpectrum.natGenerator w ≠ pr v)
    (g : GL (Fin n) ℚ) (hg1 : (g : Matrix (Fin n) (Fin n) ℚ).det = 1)
    (hg : ∀ x : Fin n → ℚ, ((gs (Fin.last V)).map (Int.castRingHom ℚ)).evalIn ℚ x =
      ((gs 0).map (Int.castRingHom ℚ)).evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x))
    (α : OAf ((gs 0).map (Int.castRingHom ℚ)))
    (hα : ∀ v ∈ P, α v ∈ Tamagawa.soSub ((gs 0).map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) ∧
      spinorNorm ((gs 0).map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) (α v) =
        sqClassOf (((∏ v ∈ S, pr v : ℕ) : ℚ) : v.adicCompletion ℚ))
    (hα1 : ∀ v, v ∉ P → α v = 1) :
    SameProperSpinorGenus ((gs 0).map (Int.castRingHom ℚ)) ⟨latOf g, latOf_isLattice g⟩
      (latSMul ((gs 0).map (Int.castRingHom ℚ)) α stdLat) := by
  classical
  have hn2 : 2 ≤ n := by omega
  revert α
  set Q := (gs 0).map (Int.castRingHom ℚ) with hQdef
  intro α hα hα1
  have hQ : Q.Nondegenerate := nondegenerate_map_of_det_ne_zero (gs 0) hd0
  let _ : MulAction (OAf Q) (Lat ℚ n) := latAction Q
  have hF1 : FormOf (gs 0) 1 (gs 0) := fun x => by simp
  have hpr : ∀ v ∈ S, ¬ ((pr v : ℕ) : ℤ) ∣ 2 * (gs 0).hessian.det := fun v hv =>
    not_dvd_two_det hP2 hPunim (hii v hv).1 (fun w hw => hprP v hv w hw)
  -- the genus along the chain
  have hgen : ∀ k (hk : k ≤ V), Siegel.SameGenus (gs 0) (gs ⟨k, by omega⟩) := by
    intro k
    induction k with
    | zero => intro _; exact Siegel.SameGenus.refl _
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      set v : Fin V := ⟨k, by omega⟩ with hv
      refine h1.trans ?_
      by_cases hvS : v ∈ S
      · exact sameGenus_of_subst hn2 (hii v hvS).1 _ _ (by
          change ¬ ((pr v : ℕ) : ℤ) ∣ 2 * (gs v.castSucc).hessian.det
          rw [hdet v.castSucc]; exact hpr v hvS)
          ((hdet v.succ).trans (hdet v.castSucc).symm) (hii v hvS).2
      · obtain ⟨U, hU, hUe⟩ := hi v hvS
        have : Siegel.IntEquiv (gs v.castSucc) (gs v.succ) :=
          (Siegel.isometricGL_iff_isometricIn _ _).mpr
            ⟨U, by rw [hU]; exact isUnit_one, fun x => (hUe x).symm⟩
        exact this.sameGenus
  have e1 : latOf (1 : GL (Fin n) ℚ) = (stdLat : Lat ℚ n).1 := by rw [latOf, glImage_one]; rfl
  have hgenL : ∀ k (hk : k ≤ V) (T : GL (Fin n) ℚ), FormOf (gs 0) T (gs ⟨k, by omega⟩) →
      SameGenus Q (stdLat : Lat ℚ n).1 (latOf T) := by
    intro k hk T hT
    rw [← e1]
    exact sameGenus_latOf_of_sameGenus hT (hgen k hk)
  -- the products of the primes below `k`
  let c : ℕ → ℕ := fun k => ∏ v ∈ S.filter (fun v : Fin V => v.1 < k), pr v
  have hc0 : c 0 = 1 := by simp [c]
  have hcne : ∀ k, c k ≠ 0 := fun k =>
    Finset.prod_ne_zero_iff.mpr fun v hv => (hii v (Finset.mem_filter.mp hv).1).1.ne_zero
  have hc_out : ∀ k (hk : k < V), (⟨k, hk⟩ : Fin V) ∉ S → c (k + 1) = c k := by
    intro k hk hvS
    refine Finset.prod_congr ?_ (fun _ _ => rfl)
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, h⟩
      refine ⟨ha, ?_⟩
      have h1 : a ≠ ⟨k, hk⟩ := fun e => hvS (e ▸ ha)
      have h2 : a.1 ≠ k := fun e => h1 (Fin.ext e)
      omega
    · rintro ⟨ha, h⟩
      exact ⟨ha, by omega⟩
  have hc_in : ∀ k (hk : k < V), (⟨k, hk⟩ : Fin V) ∈ S → c (k + 1) = c k * pr ⟨k, hk⟩ := by
    intro k hk hvS
    have : S.filter (fun v : Fin V => v.1 < k + 1) =
        insert ⟨k, hk⟩ (S.filter (fun v : Fin V => v.1 < k)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨ha, h⟩
        by_cases hak : a.1 = k
        · exact Or.inl (Fin.ext hak)
        · exact Or.inr ⟨ha, by omega⟩
      · rintro (rfl | ⟨ha, h⟩)
        · exact ⟨hvS, by simp⟩
        · exact ⟨ha, by omega⟩
    show ∏ v ∈ S.filter (fun v : Fin V => v.1 < k + 1), pr v = _
    rw [this, Finset.prod_insert (by simp [Finset.mem_filter]), mul_comm]
  have key : ∀ k (hk : k ≤ V), ∃ T : GL (Fin n) ℚ, T.val.det = 1 ∧
      FormOf (gs 0) T (gs ⟨k, by omega⟩) ∧
      ∀ β : OAf Q, CasselsGood Q P (c k) β →
        SameProperSpinorGenus Q ⟨latOf T, latOf_isLattice T⟩ (latSMul Q β stdLat) := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨1, by simp, hF1, fun β hβ => ?_⟩
      have h1 : CasselsGood Q P 1 β := by rw [hc0] at hβ; exact hβ
      have e : (⟨latOf (1 : GL (Fin n) ℚ), latOf_isLattice 1⟩ : Lat ℚ n) = stdLat := Subtype.ext e1
      rw [e]
      exact ⟨β, h1.mem_spnPlus Q hQ, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨T, hT1, hTF, hTs⟩ := ih (by omega)
      have hkV : k < V := by omega
      set v : Fin V := ⟨k, hkV⟩ with hv
      by_cases hvS : v ∈ S
      · -- a step (ii)
        obtain ⟨hp, hsub⟩ := hii v hvS
        obtain ⟨S', hS'1⟩ : ∃ G : GL (Fin n) ℚ, G.val = casselsSubstDiag n (pr v) :=
          exists_gl_of_det _ (det_casselsDiag hn2 hp.ne_zero)
        have hTS : FormOf (gs 0) (T * S') (gs ⟨k + 1, by omega⟩) := by
          intro x
          have h1 := hsub x
          rw [map_evalIn_rat, map_evalIn_rat] at h1
          have h2 := hTF (casselsSubst (pr v) x)
          have h3 : (gs v.succ).evalIn ℚ x = (gs 0).evalIn ℚ (T.val *ᵥ casselsSubst (pr v) x) :=
            h1.trans h2
          rw [casselsSubst_eq, mulVec_mulVec, ← hS'1, ← Units.val_mul] at h3
          exact h3
        refine ⟨T * S', ?_, hTS, fun β hβ => ?_⟩
        · rw [Units.val_mul, det_mul, hT1, hS'1, det_casselsDiag hn2 hp.ne_zero, one_mul]
        have hIc := casselsI_latOf_subst hn2 hp T S' hS'1
        have hcs : c (k + 1) = c k * pr v := hc_in k hkV hvS
        obtain ⟨β'', hβ''⟩ := exists_casselsGood Q hQ hn P (hcne k)
        have hαp : CasselsGood Q P (pr v) (β * β''⁻¹) := by
          have hβ' : CasselsGood Q P (pr v * c k) β := by rw [mul_comm, ← hcs]; exact hβ
          exact hβ'.split Q hQ hp.ne_zero (hcne k) hβ''
        have h4 := sameProperSpinorGenus_latSMul_of_casselsI Q hQ hn stdLat P hP2 hPunim
          (Γ := ⟨latOf (T * S'), latOf_isLattice _⟩) (Δ := ⟨latOf T, latOf_isLattice _⟩)
          (hgenL (k + 1) hk _ hTS) (hgenL k (by omega) _ hTF)
          (by
            rw [hIc]
            intro w hw hd
            exact hprP v hvS w hw
              ((Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hp).1 hd))
          (β * β''⁻¹)
          (fun w hw => by rw [hIc]; exact hαp.1 w hw) hαp.2
        have h5 := sameProperSpinorGenus_smul_left Q hQ (β * β''⁻¹) (hTs β'' hβ'')
        have e : latSMul Q (β * β''⁻¹) (latSMul Q β'' stdLat) = latSMul Q β stdLat := by
          change (β * β''⁻¹) • (β'' • (stdLat : Lat ℚ n)) = β • (stdLat : Lat ℚ n)
          rw [← mul_smul, inv_mul_cancel_right]
        rw [e] at h5
        exact SameProperSpinorGenus.trans Q h4 h5
      · -- a step (i)
        obtain ⟨U, hU, hUe⟩ := hi v hvS
        obtain ⟨V', hV'⟩ : ∃ G : GL (Fin n) ℚ, G.val = U.map (Int.castRingHom ℚ) :=
          exists_gl_of_det _ (by
            rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hU, map_one])
        have hcomp : gs v.succ = (gs v.castSucc).compMat U :=
          QuadForm.eq_of_eval_eq (fun y => by rw [QuadForm.eval_compMat]; exact hUe y)
        have hUe' : ∀ x : Fin n → ℚ, (gs v.succ).evalIn ℚ x =
            (gs v.castSucc).evalIn ℚ (U.map (Int.castRingHom ℚ) *ᵥ x) := by
          intro x
          rw [hcomp, evalIn_eq_eval_map, evalIn_eq_eval_map, ← QuadForm.map_compMat,
            QuadForm.eval_compMat]
          rfl
        have hTV : FormOf (gs 0) (T * V') (gs ⟨k + 1, by omega⟩) := by
          intro x
          have h3 : (gs v.succ).evalIn ℚ x = (gs 0).evalIn ℚ (T.val *ᵥ (V'.val *ᵥ x)) := by
            rw [hUe' x, ← hV']
            exact hTF _
          rw [mulVec_mulVec, ← Units.val_mul] at h3
          exact h3
        refine ⟨T * V', ?_, hTV, fun β hβ => ?_⟩
        · rw [Units.val_mul, det_mul, hT1, hV', ← RingHom.mapMatrix_apply, ← RingHom.map_det, hU,
            map_one, one_mul]
        have hcs : c (k + 1) = c k := hc_out k hkV hvS
        rw [hcs] at hβ
        have e : (⟨latOf (T * V'), latOf_isLattice _⟩ : Lat ℚ n) = ⟨latOf T, latOf_isLattice _⟩ :=
          Subtype.ext (latOf_mul_int T U hU V' hV')
        rw [e]
        exact hTs β hβ
  obtain ⟨T, hT1, hTF, hTs⟩ := key V le_rfl
  have hcV : c V = ∏ v ∈ S, pr v := by
    show ∏ v ∈ S.filter (fun v : Fin V => v.1 < V), pr v = _
    rw [Finset.filter_true_of_mem (fun v _ => v.2)]
  have h1 := hTs α (by rw [hcV]; exact ⟨hα, hα1⟩)
  have hTi : (T⁻¹ : GL (Fin n) ℚ).val.det = 1 := by
    have := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel T))
    rw [Units.val_mul, det_mul, hT1, Units.val_one, det_one, one_mul] at this
    exact this
  have hmem : g * T⁻¹ ∈ orthGroup Q ℚ := by
    refine mem_orthGroup_of_evalIn Q fun z => ?_
    rw [Units.val_mul, ← mulVec_mulVec, ← hg, map_evalIn_rat]
    have := hTF (T⁻¹.val *ᵥ z)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this
    exact this.trans (by rw [hQdef, map_evalIn_rat])
  have h2 : IsProperIsometric Q (latOf T) (latOf g) := by
    refine ⟨⟨g * T⁻¹, hmem⟩, ?_, ?_⟩
    · rw [Tamagawa.mem_soSub]
      show (g * T⁻¹ : GL (Fin n) ℚ).val.det = 1
      rw [Units.val_mul, det_mul, hTi, hg1, one_mul]
    · show glImage (g * T⁻¹) (latOf T) = latOf g
      show glImage (g * T⁻¹) (glImage T intVec) = glImage g intVec
      rw [← glImage_mul, inv_mul_cancel_right]
  exact SameProperSpinorGenus.trans Q (IsProperIsometric.sameProperSpinorGenus Q (IsProperIsometric.symm Q h2)) h1

/-! ### The discussion of §1 (pp. 203–204)

Cassels' introductory remark: forms of one genus are equivalent over $\mathbb Z^{(P)}$; every such equivalence is a
composition of $\mathbb Z$-equivalences and of the special substitutions (1.33) (here: `casselsSubst`), and the spinor
genus of the substituted form depends only on the multiplier and on the spinor genus of the original form. This is
proved in §§4–6 (Theorem 6.2 and its Corollary). -/

attribute [kb "cassels1978" "Ch. 11, §1, pp. 203–204 (discussion: chains of ℤ-equivalences and substitutions (1.33))"]
  Lattices.exists_chain_of_sameGenus
attribute [kb "cassels1978" "Ch. 11, §1, p. 204 (discussion: the spinor genus of h depends only on r and on that of f)"]
  Lattices.sameProperSpinorGenus_of_chain

end QuadFormsKB.Lattices
