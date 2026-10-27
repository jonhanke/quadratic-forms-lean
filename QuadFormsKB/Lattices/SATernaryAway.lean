/-
# Ternary rotations away from $\{\infty, \mathfrak p\}$ and the input `StrongApproximationSpinAt`

**Proves** `rotApproxAt_ternary` (O'Meara 1973, 104:4 step 2 away from $\mathfrak p$: from `VecApproxAt` of the quaternary
norm form) and **`strongApproximationSpinAt : StrongApproximationSpinAt F`**: for $n \ge 3$, nondegenerate $Q$ isotropic at
the finite prime $\mathfrak p$, every $h \in O'(V_{\mathbb A_f})$ is $\gamma k$ with $\gamma \in O'(V)$ and $k_\mathfrak q \in O(L_\mathfrak q)$ for
all $\mathfrak q \ne \mathfrak p$ (strong approximation with respect to $S = \{\infty, \mathfrak p\}$, applying to definite forms; the
input of Kneser's neighbour method, `Lattices/Kneser.lean`).
-/
import QuadFormsKB.Lattices.SARotAway
import QuadFormsKB.Lattices.Kneser

open NumberField IsDedekindDomain Matrix WithZero Topology Filter Quaternion
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F]

section Ternary

theorem rotApproxAt_ternary {Q : QuadForm F 3} (hQ : Q.Nondegenerate) {a b d : F} (ha : a ≠ 0) (hd : d ≠ 0)
    {P : GL (Fin 3) F} (hsim : ∀ (K : Type) [Field K] [Algebra F K] [CharZero K], SimAt Q a b d P K)
    {p : HeightOneSpectrum (𝓞 F)} (hV : VecApproxAt (Quat.nrdForm a b) p) : RotApproxAt Q p := by
  classical
  intro T hpT φ hφ U hU
  choose! α hαn hαφ using fun v (hv : v ∈ T) =>
    exists_conj_of_mem_spinorKernel hd (hsim (v.adicCompletion F)) (hφ v hv)
  set Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 4 → v.adicCompletion F) → Matrix (Fin 3) (Fin 3) (v.adicCompletion F) :=
    fun v x => PK P (v.adicCompletion F) *
      Quat.nMat (qv x : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b]) * PKi P (v.adicCompletion F)
    with hΨ
  have hΨc : ∀ v : HeightOneSpectrum (𝓞 F), Continuous (Ψ v) := fun v => continuous_conjMat v a b P
  have hmatφ : ∀ v ∈ T, omat (φ v) = Ψ v (qc (α v : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b])) := by
    intro v hv
    simp only [hΨ, qv_qc]
    refine Matrix.toLin'.injective (LinearMap.ext fun z => ?_)
    simp only [Matrix.toLin'_apply]
    have h := hαφ v hv (PKi P (v.adicCompletion F) *ᵥ z)
    rw [PK_PKi, ← LinearMap.toMatrix'_mulVec, toMatrix'_conjLin_of_nrd _ (hαn v hv)] at h
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← h, PK_PKi]
  -- good primes
  have hgood : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, GLInt P v ∧
      Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1 := by
    filter_upwards [eventually_glInt P, eventually_valuation_le_one a, eventually_valuation_le_one b]
      with v h1 h2 h3
    exact ⟨h1, by rw [valued_algebraMap]; exact h2, by rw [valued_algebraMap]; exact h3⟩
  set B := (Filter.eventually_cofinite.mp hgood).toFinset
  have hB : ∀ v, v ∉ B → GLInt P v ∧ Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1 := by
    intro v hv; by_contra hc; exact hv ((Filter.eventually_cofinite.mp hgood).mem_toFinset.mpr hc)
  choose N hN hNσ using fun v : HeightOneSpectrum (𝓞 F) => exists_mem_nhds_stdStab v Q
  set e0 : Fin 4 → F := Pi.single 0 1 with he0
  have hqe0 : ∀ v : HeightOneSpectrum (𝓞 F),
      (qv (locVec v e0) : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b]) = 1 := by
    intro v; ext <;> simp [qv, he0, locVec_apply]
  have hΨe0 : ∀ v : HeightOneSpectrum (𝓞 F), Ψ v (locVec v e0) = 1 := by
    intro v; simp only [hΨ, hqe0, nMat_one, Matrix.mul_one, PK_mul_PKi]
  have hnrde0 : (Quat.nrdForm a b).evalIn F e0 = 1 := by
    rw [Quat.evalIn_nrdForm]; simp [he0, Quat.nrd_mk]
  obtain ⟨y, hyn, hyZ, hystd⟩ := hV e0 (by rw [hnrde0]; exact one_ne_zero) (T ∪ B)
    (fun v _ _ => by
      intro i; rw [neg_zero, exp_zero, locVec_apply, he0]
      by_cases h : i = 0 <;> simp [h])
    (fun v => if v ∈ T then qc (α v : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b]) else locVec v e0)
    (by
      intro v _
      split_ifs with h
      · rw [Quat.evalIn_nrdForm, hnrde0, map_one]
        change Quat.nrd (qv (qc (α v : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b]))) = 1
        rw [qv_qc]
        try exact hαn v h
      · rw [evalIn_locVec])
    (fun v => if v ∈ T then Ψ v ⁻¹' U v else Ψ v ⁻¹' N v)
    (by
      intro v _
      split_ifs with h
      · exact (hΨc v).continuousAt.preimage_mem_nhds (by rw [← hmatφ v h]; exact hU v h)
      · exact (hΨc v).continuousAt.preimage_mem_nhds (by rw [hΨe0]; exact hN v))
  -- the global norm-one quaternion and rotation
  have hnrd1 : Quat.nrd (qv y : ℍ[F, algebraMap F F a, algebraMap F F b]) = 1 := by
    have h := Quat.evalIn_nrdForm (K := F) a b y
    rw [hyn, hnrde0] at h
    exact h.symm
  set qg : ℍ[F, algebraMap F F a, algebraMap F F b] := qv y
  set αg : (ℍ[F, algebraMap F F a, algebraMap F F b])ˣ :=
    ((Quat.isUnit_iff_nrd_ne_zero qg).mpr (by rw [hnrd1]; exact one_ne_zero)).unit
  have hαg : ((αg : (ℍ[F, algebraMap F F a, algebraMap F F b])ˣ) : ℍ[F, algebraMap F F a, algebraMap F F b]) = qg :=
    rfl
  set Mg := PK P F * Quat.nMat qg * PKi P F
  have hMg_conj : ∀ z, PKi P F *ᵥ (Mg *ᵥ (PK P F *ᵥ z)) = Quat.conjLin αg z := by
    intro z
    rw [← LinearMap.toMatrix'_mulVec, toMatrix'_conjLin_of_nrd _ (by rw [hαg]; exact hnrd1), hαg]
    simp only [Mg, ← mulVec_mulVec, PKi_PK]
  have hdetMg : Mg.det = 1 := by
    simp only [Mg, Matrix.det_mul, Quat.det_nMat, hnrd1, one_pow, mul_one]
    rw [← Matrix.det_mul, PK_mul_PKi, Matrix.det_one]
  have hNconj : ∀ w, Quat.nMat qg *ᵥ w = Quat.conjLin αg w := by
    intro w
    rw [← LinearMap.toMatrix'_mulVec, toMatrix'_conjLin_of_nrd _ (by rw [hαg]; exact hnrd1), hαg]
  have hMg_val : ∀ x, Q.evalIn F (Mg *ᵥ x) = Q.evalIn F x := by
    intro x
    have hd' : algebraMap F F d ≠ 0 := hd
    apply mul_left_cancel₀ hd'
    calc algebraMap F F d * Q.evalIn F (Mg *ᵥ x)
        = algebraMap F F d * Q.evalIn F (PK P F *ᵥ (Quat.nMat qg *ᵥ (PKi P F *ᵥ x))) := by
          simp only [Mg, mulVec_mulVec, Matrix.mul_assoc]
      _ = Quat.Q3 (algebraMap F F a) (algebraMap F F b) (Quat.nMat qg *ᵥ (PKi P F *ᵥ x)) := (hsim F _).symm
      _ = Quat.Q3 (algebraMap F F a) (algebraMap F F b) (Quat.conjLin αg (PKi P F *ᵥ x)) := by rw [hNconj]
      _ = Quat.Q3 (algebraMap F F a) (algebraMap F F b) (PKi P F *ᵥ x) := Quat.Q3_conjLin _ _
      _ = algebraMap F F d * Q.evalIn F x := Q3_PKi (hsim F) x
  set g : GL (Fin 3) F := Matrix.nonsingInvUnit Mg (by rw [hdetMg]; exact isUnit_one)
  have hgval : (g : Matrix (Fin 3) (Fin 3) F) = Mg := rfl
  have hgO : g ∈ orthGroup Q F := by
    have hSO : g ∈ Quat.SO Q := ⟨by rw [hgval]; exact hdetMg, fun x => by rw [hgval]; exact hMg_val x⟩
    have h := ((Quat.mem_SO_iff_hessian two_ne_zero).mp hSO).2
    rw [mem_orthGroup]
    have e : Q.hessian.map (algebraMap F F) = Q.hessian := by ext i j; simp
    rw [e]; exact h
  set σ : orthGroup Q F := ⟨g, hgO⟩
  have hσO' : σ ∈ spinorKernel Q F :=
    mem_spinorKernel_of_conj hd ha hQ (hsim F) (σ := σ) hdetMg (by rw [hαg]; exact hnrd1) hMg_conj
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), omat (orthMap Q (v.adicCompletion F) σ) = Ψ v (locVec v y) := by
    intro v
    rw [omat, orthMap_val]
    change (PK P F * Quat.nMat qg * PKi P F).map (algebraMap F (v.adicCompletion F)) = _
    rw [Matrix.map_mul, Matrix.map_mul, nMat_map]
    have e1 : (PK P F).map (algebraMap F (v.adicCompletion F)) = PK P (v.adicCompletion F) := by
      ext i j; simp
    have e2 : (PKi P F).map (algebraMap F (v.adicCompletion F)) = PKi P (v.adicCompletion F) := by
      ext i j; simp
    rw [e1, e2]
    rfl
  refine ⟨σ, hσO', fun v hv => ?_, fun v hv hvp => ?_⟩
  · have h := hyZ v (Finset.mem_union_left _ hv) (fun h => hpT (h ▸ hv))
    simp only [hv, ite_true, Set.mem_preimage] at h
    rw [hloc]; exact h
  · by_cases hvB : v ∈ B
    · have h := hyZ v (Finset.mem_union_right _ hvB) hvp
      simp only [hv, ite_false, Set.mem_preimage] at h
      exact hNσ v _ (by change omat _ ∈ N v; rw [hloc]; exact h)
    · obtain ⟨hP, ha', hb'⟩ := hB v hvB
      have hyv : locVec v y ∈ std v := hystd v (by simp [hv, hvB]) hvp
      refine mem_stdStab_of_conj v hP ha' hb' (q := qv (locVec v y)) ?_ ?_ (hloc v)
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [qv] <;> rw [mem_O_iff] <;>
          [have := hyv 0; have := hyv 1; have := hyv 2; have := hyv 3] <;> rwa [neg_zero, exp_zero] at this
      · have h := Quat.evalIn_nrdForm (K := v.adicCompletion F) a b (locVec v y)
        rw [evalIn_locVec] at h
        have h1 : (Quat.nrdForm a b).eval y = 1 := by rw [QuadForm.eval, hyn, hnrde0]
        rw [h1, map_one] at h
        exact h.symm

end Ternary

/-- **Ternary rotations away from $\mathfrak p$** (O'Meara 104:4 step 2): unconditional for $Q$ isotropic at $\mathfrak p$. -/
@[kb "omeara1963" "§104, proof of 104:4, step 2, pp. 317–319"]
theorem rotApproxAt_ternary_of {Q : QuadForm F 3} (hQ : Q.Nondegenerate) {p : HeightOneSpectrum (𝓞 F)}
    (hp : Q.IsotropicIn (p.adicCompletion F)) : RotApproxAt Q p := by
  obtain ⟨a, b, d, P, ha, hb, hd, hsim⟩ := exists_simAt Q hQ
  exact rotApproxAt_ternary hQ ha hd hsim (vecApproxAt_of_isotropicAt (Quat.nrdForm a b) le_rfl
    (Quat.nrdForm_nondegenerate two_ne_zero ha hb) p (isotropicIn_nrdForm (p.adicCompletion F) (hsim _) hp))

/-- **Strong approximation for rotations away from $\mathfrak p$** (O'Meara 104:4 with $S$ = all finite primes except
$\mathfrak p$): `RotApproxAt Q p` for every nondegenerate $Q$ in $n \ge 3$ variables isotropic at $\mathfrak p$. -/
@[kb "omeara1963" "§104, 104:4, pp. 315–319 (S = finite primes except 𝔭); cassels1978 Ch. 11, Thm. 8.2, p. 232"]
theorem rotApproxAt_of_isotropicAt {n : ℕ} (Q : QuadForm F n) (hn : 3 ≤ n) (hQ : Q.Nondegenerate)
    (p : HeightOneSpectrum (𝓞 F)) (hp : Q.IsotropicIn (p.adicCompletion F)) : RotApproxAt Q p := by
  rcases Nat.lt_or_ge n 4 with h3 | h4
  · obtain rfl : n = 3 := by omega
    exact rotApproxAt_ternary_of hQ hp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact rotApproxAt_of_vecApproxAt_of_four_le Q hQ h4 (vecApproxAt_of_isotropicAt Q (by omega) hQ p hp)

/-- **The input `StrongApproximationSpinAt F` holds** (Kneser 1966 via Spin; O'Meara 1973, 104:3–104:5 with
$S = \{\infty, \mathfrak p\}$): for $n \ge 3$, nondegenerate $Q$ isotropic at the finite prime $\mathfrak p$, every lattice $L$ and
every $h \in O'(V_{\mathbb A_f})$ there is $\gamma \in O'(V)$ with $(\gamma^{-1}h)_\mathfrak q L_\mathfrak q = L_\mathfrak q$ for all $\mathfrak q \ne \mathfrak p$.
Applies to definite forms (Kneser's neighbour method). -/
@[kb "omeara1963" "§104, 104:3–104:5, pp. 311–319 (S = finite primes except 𝔭); cassels1978 Ch. 11, Thm. 8.2, p. 232"]
theorem strongApproximationSpinAt : StrongApproximationSpinAt F :=
  ⟨fun Q hn hQ v hiso L h hh => approx_of_rotApproxAt Q (rotApproxAt_of_isotropicAt Q hn hQ v hiso) L h hh⟩

/-- **The global step of Kneser's theorem, unconditional** (`QuadFormsKB.exists_isometric_agree_away` with
`strongApproximationSpinAt`): every $M$ in the spinor genus of $L$ is isometric to a lattice of the spinor genus of $L$
agreeing with $L$ at every finite prime $\mathfrak q \ne \mathfrak p$ ($V_\mathfrak p$ isotropic, $n \ge 3$). -/
@[kb "kneser1957" "§2 [unverified]"]
theorem exists_isometric_agree_away_uncond {n : ℕ} (Q : QuadForm F n) (hn : 3 ≤ n) (hQ : Q.Nondegenerate)
    {v : HeightOneSpectrum (𝓞 F)} (hiso : Q.IsotropicIn (v.adicCompletion F)) {L M : Lat F n}
    (hM : SameSpinorGenus Q L M) :
    ∃ M' : Lat F n, IsIsometric Q M'.1 M.1 ∧ SameSpinorGenus Q L M' ∧ ∀ w, w ≠ v → loc w M'.1 = loc w L.1 :=
  exists_isometric_agree_away Q strongApproximationSpinAt hn hQ hiso hM

/-- **Kneser's neighbour theorem, conditional only on the local input `LocalNeighborChain F`**
(`QuadFormsKB.kneser_reach` with `strongApproximationSpinAt`). -/
@[kb "kneser1957" "§2 [unverified]"]
theorem kneser_reach_of_localChain (hLoc : LocalNeighborChain F) {n : ℕ} (Q : QuadForm F n) (hn : 3 ≤ n)
    (hQ : Q.Nondegenerate) {π : 𝓞 F} (hπ : Prime π) (h2 : ¬ π ∣ 2)
    (hiso : Q.IsotropicIn ((Nbr.hosOf hπ).adicCompletion F)) {L M : Lat F n} (hLi : IsIntegral Q L.1)
    (hLu : IsUnimodularAt Q L.1 (Nbr.hosOf hπ)) (hM : SameSpinorGenus Q L M) :
    ∃ M' : Lat F n, IsIsometric Q M'.1 M.1 ∧ Relation.ReflTransGen (Nbr.IsNbrL Q π) L.1 M'.1 :=
  kneser_reach Q strongApproximationSpinAt hLoc hn hQ hπ h2 hiso hLi hLu hM

end QuadFormsKB.Lattices
