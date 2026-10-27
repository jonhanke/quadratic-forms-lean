/-
# Hensel lifting of frames and the lattice change of frame near counts

**Layer:** a complete DVR $R$ with uniformizer $\pi$ and finite residue field (every residue characteristic, dyadic included).

**Proves**
* `exists_formF_eq_of_dvd` (**Hensel for frames**): if $\pi^d \,\Vert\, \det H_T$, $K \ge 2d+1$ and $Q\circ X \equiv T \bmod \pi^K$, then
  $Q\circ X^* = T$ for some $X^* \equiv X \bmod \pi^{K-d}$ (`newton_lift` with the differential `formD` and its
  image
  `formD_surj`; for $r = n$, $T = Q$ this is `exists_compMat_eq_of_dvd`);
* `exists_mem_of_near_frame`: a frame mod $\pi^k$ near a saturated set $A$ of genuine frames is $\pi^{k-d}$-close to $A$;
* `gNear_comp_mulVec` (**the lattice change of near counts**, abstract): for an integral $P$ on $R^\iota$ with $\pi^c R^\iota \subseteq PR^\iota$
  and $PA$ saturated, $N^{\Phi\circ P}_{k,s}(A) = |\ker(P \bmod \pi^k)|\cdot N^\Phi_{k,s}(PA)$ (the
  `nearCount_compMat`, same proof);
* `frameNear_compMat`: its frame case, $N^{Q\circ P}_{k,s}(A) = |\ker(P\bmod\pi^k)|^r\cdot N^Q_{k,s}(PA)$.

Sources: Kitaoka 1993, §5.6 [unverified]; Weil 1982, §3.4 [unverified]. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameNear
import QuadFormsKB.Tamagawa.AlphaLawIndex

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n r : ℕ}

/-- The coefficients of $T$ on and above the diagonal, indexed by `UpperIdx r`. -/
def tc (T : QuadForm R r) : UpperIdx r → R := fun p => T.coeff p.1.1 p.1.2

theorem formF_eq_tc_iff (Q : QuadForm R n) (T : QuadForm R r) (x : Fin n × Fin r → R) :
    formF Q x = tc T ↔ Q.compMat (toMat x) = T := by
  constructor
  · intro h
    refine ext_upper fun i j hij => ?_
    exact congrFun h ⟨(i, j), hij⟩
  · intro h
    funext p
    simp only [formF, tc, h]

section Hensel

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- **Exact Hensel lifting of frames** at every prime (dyadic included): if $\pi^d \,\Vert\, \det H_T$, $K \ge 2d+1$ and
$Q\circ X \equiv T \bmod \pi^K$ (coefficientwise), then $Q\circ X^* = T$ for some $X^* \equiv X \bmod \pi^{K-d}$. -/
@[kb "kitaoka1993" "§5.6 (lifting representations) [unverified]"]
theorem exists_formF_eq_of_dvd {π : R} (hπ : Irreducible π) (Q : QuadForm R n) (T : QuadForm R r) {d K : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det) (hK : 2 * d + 1 ≤ K)
    (x : Fin n × Fin r → R) (hx : ∀ p, π ^ K ∣ formF Q x p - tc T p) :
    ∃ y, formF Q y = tc T ∧ ∀ i, π ^ (K - d) ∣ y i - x i :=
  newton_lift hπ (formF Q) (formD Q) (formF_add_smul Q) (tc T) d K hK
    (fun x hx c => formD_surj Q T π hπ d K hd hd' (by omega) x hx c) x hx

/-- **Hensel and saturation for frames:** a frame $z$ with $Q\circ z \equiv T \bmod \pi^k$ that is $\equiv a \bmod \pi^s$ for some $a$
in a set $A$ of genuine frames saturated at radius $s_0$, is $\equiv a^* \bmod \pi^{k-d}$ for some $a^* \in A$. -/
theorem exists_mem_of_near_frame {π : R} (hπ : Irreducible π) (Q : QuadForm R n) (T : QuadForm R r) {d : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det)
    {A : Set (Fin n × Fin r → R)} {s₀ : ℕ}
    (hsat : ∀ a ∈ A, ∀ z, formF Q z = tc T → (∀ i, π ^ s₀ ∣ z i - a i) → z ∈ A)
    {k s : ℕ} (hs : s₀ ≤ s) (hsk : s + d ≤ k) (hk2 : 2 * d + 1 ≤ k) {z : Fin n × Fin r → R}
    (hz : ∀ p, π ^ k ∣ formF Q z p - tc T p) (hza : ∃ a ∈ A, ∀ i, π ^ s ∣ z i - a i) :
    ∃ a ∈ A, ∀ i, π ^ (k - d) ∣ z i - a i := by
  obtain ⟨a, ha, hza⟩ := hza
  obtain ⟨z', hz', hzz⟩ := exists_formF_eq_of_dvd hπ Q T hd hd' hk2 z hz
  refine ⟨z', hsat a ha z' hz' fun i => ?_, fun i => by rw [← dvd_neg, neg_sub]; exact hzz i⟩
  have h1 := (pow_dvd_pow π (show s₀ ≤ k - d by omega)).trans (hzz i)
  have h2 := (pow_dvd_pow π hs).trans (hza i)
  have := h1.add h2
  rwa [sub_add_sub_cancel] at this

end Hensel

/-! ### The lattice change of near counts -/

section LatChange

variable [Finite (IsLocalRing.ResidueField R)] {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- **$P \bmod \pi^k$** as an additive endomorphism of $(R/\pi^k)^\iota$. -/
def redMatG (π : R) (k : ℕ) (P : Matrix ι ι R) : (ι → R ⧸ Ideal.span {π ^ k}) →+ (ι → R ⧸ Ideal.span {π ^ k}) :=
  (P.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).mulVecLin.toAddMonoidHom

theorem redMatG_apply (π : R) (k : ℕ) (P : Matrix ι ι R) (z : ι → R ⧸ Ideal.span {π ^ k}) :
    redMatG π k P z = P.map (Ideal.Quotient.mk _) *ᵥ z := rfl

/-- **The lattice change of near counts**, abstract form (`nearCount_compMat` for a level map): let $P$ be
integral on
$R^\iota$ with $\pi^cR^\iota \subseteq PR^\iota$, $\Phi$ compatible with congruences, and $A$ such that every solution mod $\pi^k$ that
is $\equiv Pa \bmod \pi^s$ ($a \in A$) is $\pi^{k-e}$-close to some $Pa'$, $a' \in A$ (Hensel and saturation, `hnear`). Then for
$k \ge s + c + e$,
$$N^{\Phi\circ P}_{k,s}(A) = |\ker(P\bmod\pi^k)|\cdot N^{\Phi}_{k,s}(PA).$$ -/
@[kb "weil1982" "§3.4 (the invariant measure in the coordinates of a sublattice) [unverified]"]
theorem gNear_comp_mulVec {π : R} (hπ : Irreducible π) {Φ : (ι → R) → (κ → R)} (hΦ : IsCongr Φ π) (t : κ → R)
    (P : Matrix ι ι R) (hinj : Function.Injective (P *ᵥ · : (ι → R) → ι → R)) {c : ℕ}
    (hc : ∀ u : ι → R, ∃ w, P *ᵥ w = π ^ c • u) {A : Set (ι → R)} {k s e : ℕ}
    (hk : s + c + e ≤ k)
    (hnear : ∀ z : ι → R, (∀ p, π ^ k ∣ Φ z p - t p) → (∃ a ∈ A, ∀ i, π ^ s ∣ z i - (P *ᵥ a) i) →
      ∃ a ∈ A, ∀ i, π ^ (k - e) ∣ z i - (P *ᵥ a) i) :
    gNear (fun x => Φ (P *ᵥ x)) t π k s A = Nat.card (redMatG π k P).ker * gNear Φ t π k s ((P *ᵥ ·) '' A) := by
  classical
  have := finite_vec (ι := ι) π hπ k
  let Pred : (ι → R) → Prop := fun z =>
    (∀ p, π ^ k ∣ Φ z p - t p) ∧ ∃ a ∈ A, ∃ w : ι → R, z - P *ᵥ a = π ^ s • (P *ᵥ w)
  have hkk : π ^ s * π ^ (k - s - c) * π ^ c = π ^ k := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hPred_congr : ∀ z z', (∀ i, π ^ k ∣ z i - z' i) → Pred z → Pred z' := by
    intro z z' hzz ⟨h1, a, ha, w, hw⟩
    refine ⟨fun p => ?_, a, ha, ?_⟩
    · have := (hΦ k _ _ (fun i => by rw [← dvd_neg, neg_sub]; exact hzz i) p).add (h1 p)
      rwa [sub_add_sub_cancel] at this
    · choose u hu using fun i => (show π ^ k ∣ z' i - z i by rw [← dvd_neg, neg_sub]; exact hzz i)
      obtain ⟨w', hw'⟩ := hc u
      refine ⟨w + π ^ (k - s - c) • w', funext fun i => ?_⟩
      have h1 := congrFun hw i
      have h2 := congrFun hw' i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_add, mulVec_smul, Pi.add_apply]
      linear_combination h1 + hu i - π ^ s * π ^ (k - s - c) * h2 - u i * hkk
  have hPred_iff : ∀ z z', (∀ i, π ^ k ∣ z i - z' i) → (Pred z ↔ Pred z') := fun z z' h =>
    ⟨hPred_congr z z' h, hPred_congr z' z fun i => by rw [← dvd_neg, neg_sub]; exact h i⟩
  set Ψ := redMatG π k P
  have h1 : gNear (fun x => Φ (P *ᵥ x)) t π k s A = Nat.card (Ψ ⁻¹' {z | Pred (liftI π k z)}) := by
    unfold gNear
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    show _ ↔ Pred (liftI π k (Ψ y))
    rw [← hPred_iff (P *ᵥ liftI π k y) _ (fun i => by
      rw [← dvd_neg, neg_sub]; exact liftI_mulVec_dvd_gen π k P y i)]
    constructor
    · rintro ⟨h, a, ha, hya⟩
      choose w hw using hya
      refine ⟨h, a, ha, w, ?_⟩
      rw [← mulVec_sub, ← mulVec_smul]
      congr 1
      funext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; exact hw i
    · rintro ⟨h, a, ha, w, hw⟩
      refine ⟨h, a, ha, fun i => ⟨w i, ?_⟩⟩
      have : liftI π k y - a = π ^ s • w := hinj (by simp only; rw [mulVec_sub, mulVec_smul]; exact hw)
      have := congrFun this i
      simpa using this
  have hT : {z | Pred (liftI π k z)} ⊆ Set.range Ψ := by
    rintro z ⟨_, a, ha, w, hw⟩
    refine ⟨redI π k (a + π ^ s • w), ?_⟩
    rw [redMatG_apply, ← redI_mulVec_gen, mulVec_add, mulVec_smul, ← hw, add_sub_cancel, redI_liftI]
  have h3 : Nat.card {z | Pred (liftI π k z)} = gNear Φ t π k s ((P *ᵥ ·) '' A) := by
    unfold gNear
    refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
    show Pred (liftI π k z) ↔ _
    constructor
    · rintro ⟨h, a, ha, w, hw⟩
      refine ⟨h, P *ᵥ a, ⟨a, ha, rfl⟩, fun i => ⟨(P *ᵥ w) i, ?_⟩⟩
      have := congrFun hw i
      simpa using this
    · rintro ⟨h, _, ⟨a, ha, rfl⟩, hnr⟩
      obtain ⟨a', ha', hza'⟩ := hnear _ h ⟨a, ha, hnr⟩
      choose u hu using hza'
      obtain ⟨w', hw'⟩ := hc u
      refine ⟨h, a', ha', π ^ (k - e - s - c) • w', funext fun i => ?_⟩
      have h2 := congrFun hw' i
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_smul]
      have hpow : π ^ s * π ^ (k - e - s - c) * π ^ c = π ^ (k - e) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      linear_combination hu i - π ^ s * π ^ (k - e - s - c) * h2 - u i * hpow
  rw [h1, card_preimage_eq Ψ _ hT, h3]

end LatChange

/-! ### The level set is the disjoint union of the near sets of the orbits -/

section Partition

variable [Finite (IsLocalRing.ResidueField R)] {ι κ : Type*} [Fintype ι]

/-- **The level set mod $\pi^k$ is the disjoint union of the near sets** (abstract form of
`repCount_eq_sum_nearCount`): if the
sets $A_\tau$ ($\tau$ in a finite type) cover the exact solutions of $\Phi = t$, points of $A_\tau$, $A_{\tau'}$ congruent mod $\pi^s$ force
$\tau = \tau'$, and every solution mod $\pi^k$ is $\pi^{k-e}$-close to an exact one (`hhensel`), then for $k \ge s + e$
$$\#\{z \bmod \pi^k : \Phi(z) \equiv t\} = \sum_\tau N_{k,s}(A_\tau).$$ -/
@[kb "weil1982" "§3.4 (decomposition into orbits) [unverified]"]
theorem card_sol_eq_sum_gNear {π : R} (hπ : Irreducible π) (Φ : (ι → R) → (κ → R)) (t : κ → R)
    {ιT : Type*} [Fintype ιT] (A : ιT → Set (ι → R)) (hcover : ∀ y, Φ y = t → ∃ τ, y ∈ A τ) {s : ℕ}
    (hdisj : ∀ τ τ', ∀ a ∈ A τ, ∀ a' ∈ A τ', (∀ i, π ^ s ∣ a i - a' i) → τ = τ') {k e : ℕ} (hsk : s + e ≤ k)
    (hhensel : ∀ z : ι → R, (∀ p, π ^ k ∣ Φ z p - t p) → ∃ y, Φ y = t ∧ ∀ i, π ^ (k - e) ∣ y i - z i) :
    Nat.card {z : ι → R ⧸ Ideal.span {π ^ k} // ∀ p, π ^ k ∣ Φ (liftI π k z) p - t p} =
      ∑ τ, gNear Φ t π k s (A τ) := by
  classical
  have := finite_vec (ι := ι) π hπ k
  let P : (ι → R ⧸ Ideal.span {π ^ k}) → Prop := fun z => ∀ p, π ^ k ∣ Φ (liftI π k z) p - t p
  have hex : ∀ z : {z // P z}, ∃ τ, ∃ a ∈ A τ, ∀ i, π ^ s ∣ liftI π k z.1 i - a i := by
    intro z
    obtain ⟨y, hy, hyz⟩ := hhensel _ z.2
    obtain ⟨τ, hτ⟩ := hcover y hy
    exact ⟨τ, y, hτ, fun i => by
      rw [← dvd_neg, neg_sub]; exact (pow_dvd_pow π (by omega)).trans (hyz i)⟩
  choose τ hτ using hex
  have huniq : ∀ (z : {z // P z}) τ', (∃ a ∈ A τ', ∀ i, π ^ s ∣ liftI π k z.1 i - a i) → τ z = τ' := by
    intro z τ' ⟨a, ha, hza⟩
    obtain ⟨a', ha', hza'⟩ := hτ z
    refine hdisj _ _ a' ha' a ha fun i => ?_
    have := (hza i).sub (hza' i)
    rwa [show liftI π k z.1 i - a i - (liftI π k z.1 i - a' i) = a' i - a i by ring] at this
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv τ), Nat.card_sigma]
  refine Finset.sum_congr rfl fun τ' _ => Nat.card_congr ?_
  exact
    { toFun := fun z => ⟨z.1.1, z.1.2, by have := hτ z.1; rw [z.2] at this; exact this⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, huniq ⟨z.1, z.2.1⟩ τ' z.2.2⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl }

end Partition

/-! ### Frames: the lattice change and the invariance under an isometry -/

section FrameChange

variable [Finite (IsLocalRing.ResidueField R)] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

theorem frameMat_mulVec_col {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A) (x : Fin n × Fin r → A)
    (i : Fin n) (j : Fin r) : (frameMat r M *ᵥ x) (i, j) = (M *ᵥ fun l => x (l, j)) i := by
  rw [frameMat_mulVec]; simp [mulVec, dotProduct]

theorem frameMat_injective (P : Matrix (Fin n) (Fin n) R) (hP : P.det ≠ 0) :
    Function.Injective (frameMat r P *ᵥ · : (Fin n × Fin r → R) → _) := by
  intro x y hxy
  funext ⟨i, j⟩
  have := mulVec_injective_of_det_ne_zero P hP (a₁ := fun l => x (l, j)) (a₂ := fun l => y (l, j)) (by
    funext i
    have := congrFun hxy (i, j)
    simp only [frameMat_mulVec_col] at this
    exact this)
  exact congrFun this i

theorem frameMat_hc (P : Matrix (Fin n) (Fin n) R) {π : R} {c : ℕ} (hc : ∀ u : Fin n → R, ∃ w, P *ᵥ w = π ^ c • u)
    (u : Fin n × Fin r → R) : ∃ w, frameMat r P *ᵥ w = π ^ c • u := by
  choose w hw using fun j : Fin r => hc (fun l => u (l, j))
  refine ⟨fun p => w p.2 p.1, funext fun ⟨i, j⟩ => ?_⟩
  rw [frameMat_mulVec_col]
  have := congrFun (hw j) i
  simpa using this

theorem card_ker_redMat_eq {π : R} (hπ : Irreducible π) (P : Matrix (Fin n) (Fin n) R) (hP : P.det ≠ 0) {c k : ℕ}
    (hc : ∀ u : Fin n → R, ∃ w, P *ᵥ w = π ^ c • u) (hck : c ≤ k) :
    Nat.card (redMat π k P).ker = Nat.card (R ⧸ Ideal.span {P.det}) := by
  rw [card_ker_redMat hπ P (k := k) ?_, card_quot_range hπ P hP]
  intro u
  obtain ⟨w, hw⟩ := hc u
  refine ⟨π ^ (k - c) • w, ?_⟩
  rw [mulVec_smul, hw, smul_smul, ← pow_add, Nat.sub_add_cancel hck]

/-- $|\ker(P \bmod \pi^k)|$ on frames is the $r$-th power of $|\ker(P\bmod\pi^k)|$ on vectors (the action is columnwise). -/
theorem card_ker_frameMat (π : R) (k : ℕ) (P : Matrix (Fin n) (Fin n) R) :
    Nat.card (redMatG π k (frameMat r P)).ker = Nat.card (redMat π k P).ker ^ r := by
  have key : ∀ x : Fin n × Fin r → R ⧸ Ideal.span {π ^ k},
      x ∈ (redMatG π k (frameMat r P)).ker ↔ ∀ j, (fun l => x (l, j)) ∈ (redMat π k P).ker := by
    intro x
    simp only [AddMonoidHom.mem_ker, redMatG_apply, redMat_apply, frameMat_map]
    constructor
    · intro h j
      funext i
      have := congrFun h (i, j)
      rwa [frameMat_mulVec_col] at this
    · intro h
      funext ⟨i, j⟩
      rw [frameMat_mulVec_col]
      exact congrFun (h j) i
  let e : (redMatG π k (frameMat r P)).ker ≃ (Fin r → (redMat π k P).ker) :=
    { toFun := fun x j => ⟨fun l => x.1 (l, j), (key x.1).1 x.2 j⟩
      invFun := fun f => ⟨fun p => (f p.2).1 p.1, (key _).2 fun j => by simp⟩
      left_inv := fun x => by ext ⟨i, j⟩; rfl
      right_inv := fun f => by funext j; ext i; rfl }
  rw [Nat.card_congr e]
  simp [Nat.card_pi]

/-- **Two bases of lattices with the same Gram form and associated determinants give the same near counts** (the finite form of
the invariance of Weil's measure on the frames of $T$ under $O(V)$; it replaces the involution argument
`nearCount_eq_of_involution`).
Let $P_1, P_2$ be integral, $\det P_i \ne 0$, $\det P_1$ and $\det P_2$ associated, $\pi^cR^n \subseteq P_iR^n$, and $Q\circ P_1 = Q\circ P_2$
(over $F_\mathfrak p$: $P_2 = hP_1$ for an isometry $h$). If $P_1A$ and $P_2A$ are saturated at radius $s_0$ among the frames of $T$ for $Q$
($\pi^d\,\Vert\,\det H_T$), then for $s \ge s_0$, $k \ge s + c + d$, $k \ge 2d + 1$,
$$N^Q_{k,s}(P_1A) = N^Q_{k,s}(P_2A).$$
*Proof:* both are $|\ker(P_i\bmod\pi^k)|^{-r}N^{Q\circ P_i}_{k,s}(A)$ (`gNear_comp_mulVec` with Hensel and saturation), the counts
$N^{Q\circ P_1} = N^{Q\circ P_2}$ agree, and $|\ker(P_i\bmod\pi^k)| = \#R/(\det P_i)$ (`card_ker_redMat`, `card_quot_range`). -/
@[kb "weil1982" "§3.4 (invariance of the orbit measure under O(V)) [unverified]"]
theorem frameNear_eq_of_compMat_eq {π : R} (hπ : Irreducible π) (Q : QuadForm R n) (T : QuadForm R r) {d : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det)
    {P₁ P₂ : Matrix (Fin n) (Fin n) R} (hP₁ : P₁.det ≠ 0) (hP₂ : P₂.det ≠ 0) (hdet : Associated P₁.det P₂.det)
    (hQ : Q.compMat P₁ = Q.compMat P₂) {c : ℕ} (hc₁ : ∀ u : Fin n → R, ∃ w, P₁ *ᵥ w = π ^ c • u)
    (hc₂ : ∀ u : Fin n → R, ∃ w, P₂ *ᵥ w = π ^ c • u) {A : Set (Fin n × Fin r → R)} {s₀ : ℕ}
    (hsat₁ : ∀ a ∈ A, ∀ z, formF Q z = tc T → (∀ i, π ^ s₀ ∣ z i - (frameMat r P₁ *ᵥ a) i) →
      ∃ a' ∈ A, z = frameMat r P₁ *ᵥ a')
    (hsat₂ : ∀ a ∈ A, ∀ z, formF Q z = tc T → (∀ i, π ^ s₀ ∣ z i - (frameMat r P₂ *ᵥ a) i) →
      ∃ a' ∈ A, z = frameMat r P₂ *ᵥ a')
    {k s : ℕ} (hs : s₀ ≤ s) (hk : s + c + d ≤ k) (hk2 : 2 * d + 1 ≤ k) :
    gNear (formF Q) (tc T) π k s ((frameMat r P₁ *ᵥ ·) '' A) =
      gNear (formF Q) (tc T) π k s ((frameMat r P₂ *ᵥ ·) '' A) := by
  have := finite_vec (ι := Fin n × Fin r) π hπ k
  have key : ∀ (P : Matrix (Fin n) (Fin n) R), P.det ≠ 0 → (∀ u : Fin n → R, ∃ w, P *ᵥ w = π ^ c • u) →
      (∀ a ∈ A, ∀ z, formF Q z = tc T → (∀ i, π ^ s₀ ∣ z i - (frameMat r P *ᵥ a) i) →
        ∃ a' ∈ A, z = frameMat r P *ᵥ a') →
      gNear (fun x => formF Q (frameMat r P *ᵥ x)) (tc T) π k s A =
        Nat.card (redMatG π k (frameMat r P)).ker * gNear (formF Q) (tc T) π k s ((frameMat r P *ᵥ ·) '' A) := by
    intro P hP hc hsat
    refine gNear_comp_mulVec hπ (isCongr_formF Q π) (tc T) (frameMat r P) (frameMat_injective P hP)
      (frameMat_hc P hc) (e := d) hk ?_
    intro z hz hza
    obtain ⟨a, ha, haz⟩ := hza
    have hsat' : ∀ b ∈ (frameMat r P *ᵥ ·) '' A, ∀ z, formF Q z = tc T → (∀ i, π ^ s₀ ∣ z i - b i) →
        z ∈ (frameMat r P *ᵥ ·) '' A := by
      rintro _ ⟨a, ha, rfl⟩ z hz hza
      obtain ⟨a', ha', rfl⟩ := hsat a ha z hz hza
      exact ⟨a', ha', rfl⟩
    obtain ⟨_, ⟨a', ha', rfl⟩, h⟩ := exists_mem_of_near_frame hπ Q T hd hd' hsat' hs (by omega) hk2 hz
      ⟨_, ⟨a, ha, rfl⟩, haz⟩
    exact ⟨a', ha', h⟩
  have h1 := key P₁ hP₁ hc₁ hsat₁
  have h2 := key P₂ hP₂ hc₂ hsat₂
  simp only [formF_frameMat, hQ] at h1 h2
  have hK : Nat.card (redMatG π k (frameMat r P₁)).ker = Nat.card (redMatG π k (frameMat r P₂)).ker := by
    rw [card_ker_frameMat, card_ker_frameMat, card_ker_redMat_eq hπ P₁ hP₁ hc₁ (by omega),
      card_ker_redMat_eq hπ P₂ hP₂ hc₂ (by omega), Ideal.span_singleton_eq_span_singleton.mpr hdet]
  have hpos : 0 < Nat.card (redMatG π k (frameMat r P₁)).ker := Nat.card_pos
  rw [← hK] at h2
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)

end FrameChange

end QuadFormsKB.Tamagawa.Frames
