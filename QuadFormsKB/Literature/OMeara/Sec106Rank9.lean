/-
# O'Meara §106B, §106D–F: the unimodular lattices of rank at most $9$, unconditionally

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^n$ with $Q = x_0^2 + \dots + x_{n-1}^2$ (`sumSqForm n`, O'Meara's $I_n$), lattices
`Lat ℚ n`, unimodular lattices `IsUnimodularZ`, $\mathcal G(D)$ = `omearaG`, $D = \mathbb Z^n$ = `intVec`, $E$ = `omearaE n`,
$E_8 \perp \mathbb Z^{n-8}$ = `omearaEZ n`, adjacency = `Nbr.IsNbrL Q 2`. Indices are 0-based.

**Defines** `omearaEPerp m n` ($E_m \perp \mathbb Z^{n-m}$, general form of `omearaEZ`; `omearaEPerp 8 n = omearaEZ n`),
`OMeara106_r38` (named statement, Kneser's classification for $n \le 13$, stated, never assumed), and auxiliary
`spExt`, `splitLat`, `blkMat`, `blkGL`, `Ecrit`.

**Proves** (all unconditional, no `sorry`)
* `omeara106_2` (**106:2**, p. 325): the named statement `OMeara106_2` holds (`omeara106_2_holds` of `Sec106Two.lean`:
  strong approximation away from $2$, not Theorem 104:10); `omeara106_10_uncond` (**106:10**, $1 \le n \le 7$,
  unconditional).
* `omeara106_r25` (**106.r25**, p. 327): for $n \ge 5$ a finite set of lattices of $\mathcal G(D)$ meets every proper
  class of unimodular lattices on $I_n$ (finiteness of classes, `ClassFin.classes_finite`, and 106:2).
* `unimodular_split_unit` (p. 330, "$L$ represents $1$, hence splits"): a unimodular lattice on $I_{k+1}$ containing a vector
  of norm $1$ is $\sigma^{-1}(L' \perp \mathbb Z)$ with $L'$ unimodular on $I_k$; `unimodular_split_isIsometric` (with
  106:10 for $k = 7$, `isIsometric_of_norm_one_rank8`).
* `omeara106_12` (**106:12**, p. 333): a unimodular lattice adjacent to $E$ ($n = 8$) is in the class of $D$ or of $E$.
* `omeara106_13` (**106:13**, p. 334): for $1 \le n \le 9$ a unimodular lattice on $I_n$ is isometric to exactly one of
  $\mathbb Z^n$, $E_8 \perp \mathbb Z^{n-8}$ ($n \ge 8$); the cases $n = 8, 9$ are `unimodular_rank8`, `unimodular_rank9`.

**Deviations from the book's proofs.** (1) 106:12: instead of O'Meara's four cases (reducing $z$ modulo $L \cap E$ by
106:8) the key dichotomy `key_norm_one` (a vector $w$ of norm $1$ with $z - w \in E$ gives either $w \in L$ or
$\tau_wL = E$) is combined with the covering lemma `nt8`/`exists_unit_vec_E`, a single integer computation
(for $n = 8$ the vector $w$ is written down: $\tfrac14 d$ with $\sum d_i^2 = 16$). (2) Adjacent to $D$ (the first step of
the chain in 106:13): `omeara_adj_D_rank8` counts the odd coordinates of $2y$ (four or eight) instead of the
book's "splits / does not split" dichotomy; with eight odd coordinates the lattice is isometric to $E$ by the sign-change
argument of 106.r30 (`isIsometric_E_of_all_odd`, improper isometries allowed). (3) The isometry classes ($\mathrm{cls}$,
`IsIsometric`) rather than proper classes are used in 106:12 and 106:13, as in the book's statements.
-/
import QuadFormsKB.Literature.OMeara.Sec106Class
import QuadFormsKB.Literature.OMeara.Sec106Two
import QuadFormsKB.Literature.OMeara.Sec106EZ
import QuadFormsKB.Literature.OMeara.Sec106Facts

open Matrix NumberField IsDedekindDomain QuadFormsKB.HilbertModular

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### 106:2 and 106:10, unconditionally -/

/-- **Proposition 106:2 — proved** (O'Meara 1973, §106B, p. 325). For $n \ge 5$ and unimodular lattices $K, L$ on
$V = I_n$ over $\mathbb Q$, the proper class of $K$ meets $\mathcal G(L)$. This is the named statement `OMeara106_2`,
established by `omeara106_2_holds` (`Sec106Two.lean`) with strong approximation away from $2$ (the library's
`strongApproximationSpinAt`), not via Theorem 104:10 over $\mathbb Z[\tfrac12]$ as in the book. Unconditional. -/
@[kb "omeara1963" "§106B, 106:2, p. 325"]
theorem omeara106_2 : OMeara106_2 := ⟨omeara106_2_holds⟩

/-- **Proposition 106:10, unconditional** (O'Meara 1973, §106D, p. 330): for $1 \le n \le 7$, every unimodular
lattice $L$ on $V = I_n$ over $\mathbb Q$ (`hL : IsUnimodularZ (sumSqForm n) L.1`) has matrix $I_n$, i.e. is isometric
to $D = \mathbb Z^n$ (`IsIsometric (sumSqForm n) intVec L.1`). This is `omeara106_10` (conditional on `OMeara106_2`)
with `omeara106_2` supplied. -/
@[kb "omeara1963" "§106D, 106:10, p. 330"]
theorem omeara106_10_uncond {n : ℕ} (h1 : 1 ≤ n) (h7 : n ≤ 7) {L : Lat ℚ n}
    (hL : IsUnimodularZ (sumSqForm n) L.1) : IsIsometric (sumSqForm n) intVec L.1 :=
  omeara106_10 omeara106_2 h1 h7 hL

/-! ### 106.r25: finitely many proper classes, all met by $\mathcal G(D)$ -/

private lemma r9_unimod_integral {n : ℕ} {L : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hL : IsUnimodularZ (sumSqForm n) L) : IsIntegral (sumSqForm n) L :=
  isIntegral_of_unimodular hL

private lemma r9_unimod_dualBounded {n : ℕ} {L : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hL : IsUnimodularZ (sumSqForm n) L) : ClassFin.IsDualBounded (sumSqForm n) L 2 := by
  intro x hx
  have h2x : (2 : ℤ) • x ∈ omearaDual (sumSqForm n) L := by
    intro m hm
    obtain ⟨a, ha⟩ := hx m hm
    obtain ⟨k, hk⟩ : ∃ k : ℤ, ((k : ℤ) : 𝓞 ℚ) = a :=
      ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩
    refine ⟨k, ?_⟩
    have e : (2 : ℤ) • x = ((2 : ℤ) : ℚ) • x := (Int.cast_smul_eq_zsmul ℚ 2 x).symm
    rw [e, bil_smul_left']
    have h0 : algebraMap (𝓞 ℚ) ℚ a = k := by rw [← hk]; simp
    have : bil (sumSqForm n) x m = k := ha.symm.trans h0
    rw [this]
    push_cast
    ring
  rwa [hL] at h2x

/-- An improper isometry of $I_n$ ($n \ge 1$): the reflection in $x_0$. -/
private lemma r9_exists_improper {n : ℕ} (hn : 1 ≤ n) :
    ∃ τ : orthGroup (sumSqForm n) ℚ, ((τ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = -1 := by
  have hev : (sumSqForm n).evalIn ℚ (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℚ)) ≠ 0 := by
    have : (sumSqForm n).evalIn ℚ (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℚ)) = 1 := by
      rw [sumSqForm, QuadForm.evalIn_diag]
      simp [Pi.single_apply]
    rw [this]; exact one_ne_zero
  exact ⟨symm (sumSqForm n) ℚ _, symm_det _ ℚ hev⟩

private lemma r9_uni_image {n : ℕ} {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup (sumSqForm n) ℚ)
    {L : Lat ℚ n} (hL : IsUnimodularZ (sumSqForm n) L.1) :
    IsUnimodularZ (sumSqForm n) (Lat.image γ L).1 := by
  show omearaDual (sumSqForm n) (glImage γ L.1) = glImage γ L.1
  rw [omearaDual_glImage _ hγ, show omearaDual (sumSqForm n) L.1 = L.1 from hL]

/-- **106.r25** (O'Meara 1973, §106B, p. 327): for $n \ge 5$ there is a finite set $S$ of lattices in
$\mathcal G(D)$ ($D = \mathbb Z^n$, `intVec`) such that every unimodular lattice $L$ on $V = I_n$ is properly isometric
(`IsProperIsometric`, by a rotation) to a member of $S$.

*Proof.* The unimodular lattices on $I_n$ are integral with bounded dual ($2L^\# \subseteq L$ for the form
$B = \tfrac12$ `bil`), so by the finiteness of classes (O'Meara 103:4, `ClassFin.classes_finite`) they fall into finitely
many isometry classes. For a representative $R$ of each class take, by 106:2 (`omeara106_2`), a lattice $J \in
\mathcal G(D)$ properly isometric to $R$, and likewise $J'$ for $\tau R$ with $\tau$ the reflection in $x_0$ (an improper
isometry of $I_n$). A lattice $L = \gamma R$ is then properly isometric to $J$ (if $\det\gamma = 1$) or to $J'$ (if
$\det\gamma = -1$, as $L = (\gamma\tau)\tau R$): at most two proper classes per class. -/
@[kb "omeara1963" "§106B, 106.r25, p. 327 (finitely many proper classes, all represented in G(D))"]
theorem omeara106_r25 (n : ℕ) (hn : 5 ≤ n) :
    ∃ S : Finset (Lat ℚ n),
      (∀ K ∈ S, K ∈ omearaG (sumSqForm n) (⟨intVec, intVec_isLattice⟩ : Lat ℚ n)) ∧
      ∀ L : Lat ℚ n, IsUnimodularZ (sumSqForm n) L.1 →
        ∃ K ∈ S, IsProperIsometric (sumSqForm n) L.1 K.1 := by
  classical
  have hQ : (sumSqForm n).Nondegenerate := QuadForm.nondegenerate_diag (fun _ => one_ne_zero)
  let D : Lat ℚ n := ⟨intVec, intVec_isLattice⟩
  have hD : IsUnimodularZ (sumSqForm n) D.1 := adj_D_unimodular
  have hfin := ClassFin.classes_finite hQ (c := 2) two_ne_zero
  set T : Set (LatClass (sumSqForm n)) :=
    {c | ∃ M : Lat ℚ n, Quotient.mk (latSetoid (sumSqForm n)) M = c ∧ IsUnimodularZ (sumSqForm n) M.1} with hTdef
  have hT : T.Finite := hfin.subset (by
    rintro c ⟨M, hM, hu⟩
    exact ⟨M, hM, r9_unimod_integral hu, r9_unimod_dualBounded hu⟩)
  obtain ⟨τ, hτdet⟩ := r9_exists_improper (n := n) (by omega)
  have hτ : (τ : GL (Fin n) ℚ) ∈ orthGroup (sumSqForm n) ℚ := τ.2
  -- for each class, two lattices in G(D)
  have hex : ∀ c : T, ∃ p : Lat ℚ n × Lat ℚ n, p.1 ∈ omearaG (sumSqForm n) D ∧ p.2 ∈ omearaG (sumSqForm n) D ∧
      ∀ L : Lat ℚ n, Quotient.mk (latSetoid (sumSqForm n)) L = c.1 →
        IsProperIsometric (sumSqForm n) L.1 p.1.1 ∨ IsProperIsometric (sumSqForm n) L.1 p.2.1 := by
    rintro ⟨c, M, hMc, hMu⟩
    obtain ⟨J, hJp, hJG⟩ := omeara106_2.holds n hn M D hMu hD
    obtain ⟨J', hJ'p, hJ'G⟩ := omeara106_2.holds n hn (Lat.image (τ : GL (Fin n) ℚ) M) D
      (r9_uni_image hτ hMu) hD
    refine ⟨(J, J'), hJG, hJ'G, fun L hL => ?_⟩
    have hLM : IsIsometric (sumSqForm n) L.1 M.1 := by
      have := Quotient.exact (hL.trans hMc.symm)
      exact this
    obtain ⟨γ, hγ, hγL⟩ := hLM
    rcases Tamagawa.det_eq_one_or_neg_one (sumSqForm n) hQ (⟨γ, hγ⟩ : orthGroup (sumSqForm n) ℚ) with h1 | h1
    · left
      exact IsProperIsometric.trans _ ⟨⟨γ, hγ⟩, Tamagawa.mem_soSub.mpr h1, hγL⟩ hJp
    · right
      refine IsProperIsometric.trans _ ⟨τ * ⟨γ, hγ⟩, ?_, ?_⟩ hJ'p
      · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul]
        change ((τ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det * γ.val.det = 1
        rw [hτdet, h1]
        norm_num
      · rw [Subgroup.coe_mul, glImage_mul]
        change glImage (τ : GL (Fin n) ℚ) (glImage γ L.1) = glImage (τ : GL (Fin n) ℚ) M.1
        rw [hγL]
  have : Fintype T := hT.fintype
  choose f hf1 hf2 hf3 using hex
  refine ⟨Finset.univ.image (fun c => (f c).1) ∪ Finset.univ.image (fun c => (f c).2), ?_, ?_⟩
  · intro K hK
    rcases Finset.mem_union.mp hK with h | h
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp h
      exact hf1 c
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp h
      exact hf2 c
  · intro L hL
    have hc : Quotient.mk (latSetoid (sumSqForm n)) L ∈ T := ⟨L, rfl, hL⟩
    rcases hf3 ⟨_, hc⟩ L rfl with h | h
    · exact ⟨(f ⟨_, hc⟩).1, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)), h⟩
    · exact ⟨(f ⟨_, hc⟩).2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)), h⟩

/-! ### Splitting off a vector of norm $1$ -/

section Split

private lemma r9_eval {n : ℕ} (x : Fin n → ℚ) : (sumSqForm n).eval x = ∑ i, x i ^ 2 := by
  rw [sumSqForm, QuadForm.eval, QuadForm.evalIn_diag]; simp

private lemma r9_bil {n : ℕ} (x y : Fin n → ℚ) : bil (sumSqForm n) x y = 2 * ∑ i, x i * y i := by
  have h : (sumSqForm n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
    · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]
  rw [bil, h, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, dotProduct, smul_eq_mul]

/-- **The vector $(u, t)$**: $u \in \mathbb Q^k$ with the coordinate $t$ appended (index $k$). Auxiliary. -/
def spExt {k : ℕ} (u : Fin k → ℚ) (t : ℚ) : Fin (k + 1) → ℚ := Fin.snoc (α := fun _ => ℚ) u t

@[simp] lemma spExt_castSucc {k : ℕ} (u : Fin k → ℚ) (t : ℚ) (i : Fin k) :
    spExt u t (Fin.castSucc i) = u i := by simp [spExt]

@[simp] lemma spExt_last {k : ℕ} (u : Fin k → ℚ) (t : ℚ) : spExt u t (Fin.last k) = t := by simp [spExt]

lemma spExt_eta {k : ℕ} (z : Fin (k + 1) → ℚ) :
    z = spExt (fun i => z (Fin.castSucc i)) (z (Fin.last k)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma spExt_add {k : ℕ} (u v : Fin k → ℚ) (s t : ℚ) : spExt (u + v) (s + t) = spExt u s + spExt v t := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma spExt_smul {k : ℕ} (c : ℚ) (u : Fin k → ℚ) (t : ℚ) : spExt (c • u) (c * t) = c • spExt u t := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

private lemma r9_sum_succ {k : ℕ} (f : Fin (k + 1) → ℚ) :
    ∑ i, f i = ∑ i : Fin k, f (Fin.castSucc i) + f (Fin.last k) := Fin.sum_univ_castSucc f

lemma bil_spExt {k : ℕ} (u v : Fin k → ℚ) (s t : ℚ) :
    bil (sumSqForm (k + 1)) (spExt u s) (spExt v t) = bil (sumSqForm k) u v + 2 * (s * t) := by
  rw [r9_bil, r9_bil, r9_sum_succ]
  simp only [spExt_castSucc, spExt_last]
  ring

/-- **The lattice $L' \perp \mathbb Z$ in $\mathbb Q^{k+1}$**: the vectors $z$ whose first $k$ coordinates lie in
$L' \subseteq \mathbb Q^k$ and whose last coordinate is an integer. Auxiliary. -/
def splitLat {k : ℕ} (L' : Submodule (𝓞 ℚ) (Fin k → ℚ)) : Submodule (𝓞 ℚ) (Fin (k + 1) → ℚ) where
  carrier := {z | (fun i => z (Fin.castSucc i)) ∈ L' ∧ ∃ m : ℤ, z (Fin.last k) = m}
  add_mem' {x y} hx hy := by
    obtain ⟨a, ha⟩ := hx.2
    obtain ⟨b, hb⟩ := hy.2
    exact ⟨L'.add_mem hx.1 hy.1, a + b, by simp [ha, hb]⟩
  zero_mem' := ⟨L'.zero_mem, 0, by simp⟩
  smul_mem' c x hx := by
    obtain ⟨j, hj⟩ := exists_int_smul_eq c x
    obtain ⟨a, ha⟩ := hx.2
    rw [hj]
    refine ⟨?_, j * a, by simp [ha]⟩
    have : (fun i => ((j : ℚ) • x) (Fin.castSucc i)) = (j : ℚ) • (fun i => x (Fin.castSucc i)) := by
      funext i; simp
    rw [this]
    exact intCast_smul_mem hx.1 j

lemma mem_splitLat {k : ℕ} {L' : Submodule (𝓞 ℚ) (Fin k → ℚ)} {z : Fin (k + 1) → ℚ} :
    z ∈ splitLat L' ↔ (fun i => z (Fin.castSucc i)) ∈ L' ∧ ∃ m : ℤ, z (Fin.last k) = m := Iff.rfl

lemma bil_eta_right {k : ℕ} (x : Fin (k + 1) → ℚ) (v : Fin k → ℚ) (t : ℚ) :
    bil (sumSqForm (k + 1)) x (spExt v t) =
      bil (sumSqForm k) (fun i => x (Fin.castSucc i)) v + 2 * (x (Fin.last k) * t) := by
  have := bil_spExt (fun i => x (Fin.castSucc i)) v (x (Fin.last k)) t
  rwa [← spExt_eta x] at this

lemma bil_eta_left {k : ℕ} (u : Fin k → ℚ) (s : ℚ) (y : Fin (k + 1) → ℚ) :
    bil (sumSqForm (k + 1)) (spExt u s) y =
      bil (sumSqForm k) u (fun i => y (Fin.castSucc i)) + 2 * (s * y (Fin.last k)) := by
  have := bil_spExt u (fun i => y (Fin.castSucc i)) s (y (Fin.last k))
  rwa [← spExt_eta y] at this

private lemma r9_bil_zero_right {n : ℕ} (x : Fin n → ℚ) : bil (sumSqForm n) x 0 = 0 := by
  simp [bil]

private lemma r9_spExt_zero_mem {k : ℕ} (L' : Submodule (𝓞 ℚ) (Fin k → ℚ)) :
    (fun i : Fin k => (spExt (0 : Fin k → ℚ) 1) (Fin.castSucc i)) ∈ L' := by
  have : (fun i : Fin k => (spExt (0 : Fin k → ℚ) 1) (Fin.castSucc i)) = 0 := by
    funext i; simp
  rw [this]; exact L'.zero_mem

/-- **$L' \perp \mathbb Z$ is unimodular if $L'$ is** (auxiliary). -/
theorem splitLat_unimodular {k : ℕ} {L' : Submodule (𝓞 ℚ) (Fin k → ℚ)}
    (hL' : IsUnimodularZ (sumSqForm k) L') : IsUnimodularZ (sumSqForm (k + 1)) (splitLat L') := by
  unfold IsUnimodularZ
  ext x
  constructor
  · intro hx
    have he : (spExt (0 : Fin k → ℚ) 1) ∈ splitLat L' := ⟨r9_spExt_zero_mem L', 1, by simp⟩
    obtain ⟨m, hm⟩ := hx _ he
    rw [bil_eta_right, r9_bil_zero_right] at hm
    refine ⟨?_, m, by linarith⟩
    rw [← hL']
    intro v hv
    have hv' : spExt v 0 ∈ splitLat L' := ⟨by simpa using hv, 0, by simp⟩
    obtain ⟨m', hm'⟩ := hx _ hv'
    rw [bil_eta_right] at hm'
    exact ⟨m', by linarith⟩
  · intro hx y hy
    obtain ⟨hx1, a, ha⟩ := hx
    obtain ⟨hy1, b, hb⟩ := hy
    obtain ⟨m, hm⟩ := uni_mem' _ hL' hx1 hy1
    refine ⟨m + a * b, ?_⟩
    have := bil_spExt (fun i => x (Fin.castSucc i)) (fun i => y (Fin.castSucc i)) (x (Fin.last k))
      (y (Fin.last k))
    rw [← spExt_eta x, ← spExt_eta y] at this
    rw [this, ha, hb]
    push_cast
    linarith

/-! #### Block-diagonal isometries -/

/-- The block matrix $\mathrm{diag}(A, 1)$ of size $k + 1$. Auxiliary. -/
def blkMat {k : ℕ} (A : Matrix (Fin k) (Fin k) ℚ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of fun i j => spExt (fun i' => spExt (fun j' => A i' j') 0 j) (if j = Fin.last k then 1 else 0) i

lemma blkMat_mulVec {k : ℕ} (A : Matrix (Fin k) (Fin k) ℚ) (z : Fin (k + 1) → ℚ) :
    blkMat A *ᵥ z = spExt (A *ᵥ (fun i => z (Fin.castSucc i))) (z (Fin.last k)) := by
  funext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [blkMat, Matrix.mulVec, dotProduct]
  · simp [blkMat, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

private lemma r9_mat_ext {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℚ} (h : ∀ z, M *ᵥ z = N *ᵥ z) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun z => by simpa using h z)

lemma blkMat_mul {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℚ) : blkMat A * blkMat B = blkMat (A * B) := by
  refine r9_mat_ext fun z => ?_
  rw [← Matrix.mulVec_mulVec, blkMat_mulVec, blkMat_mulVec, blkMat_mulVec]
  simp [Matrix.mulVec_mulVec]

lemma blkMat_one {k : ℕ} : blkMat (1 : Matrix (Fin k) (Fin k) ℚ) = 1 := by
  refine r9_mat_ext fun z => ?_
  rw [blkMat_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]
  exact (spExt_eta z).symm

/-- The block diagonal element $\mathrm{diag}(\gamma, 1) \in \mathrm{GL}_{k+1}(\mathbb Q)$. Auxiliary. -/
def blkGL {k : ℕ} (γ : GL (Fin k) ℚ) : GL (Fin (k + 1)) ℚ :=
  ⟨blkMat γ.val, blkMat (γ⁻¹).val, by rw [blkMat_mul, Units.mul_inv, blkMat_one],
    by rw [blkMat_mul, Units.inv_mul, blkMat_one]⟩

lemma blkGL_mulVec {k : ℕ} (γ : GL (Fin k) ℚ) (z : Fin (k + 1) → ℚ) :
    (blkGL γ).val *ᵥ z = spExt (γ.val *ᵥ (fun i => z (Fin.castSucc i))) (z (Fin.last k)) :=
  blkMat_mulVec _ z

lemma blkGL_mem_orth {k : ℕ} {γ : GL (Fin k) ℚ} (hγ : γ ∈ orthGroup (sumSqForm k) ℚ) :
    blkGL γ ∈ orthGroup (sumSqForm (k + 1)) ℚ := by
  refine mem_orthGroup_of_eval _ fun z => ?_
  rw [blkGL_mulVec, r9_eval, r9_eval, r9_sum_succ, r9_sum_succ]
  simp only [spExt_castSucc, spExt_last]
  have := evalIn_mulVec_of_mem (sumSqForm k) hγ (fun i => z (Fin.castSucc i))
  have h2 : ∑ i, ((γ.val *ᵥ fun i => z (Fin.castSucc i)) i) ^ 2 = ∑ i : Fin k, (z (Fin.castSucc i)) ^ 2 := by
    have h3 := this
    change (sumSqForm k).eval _ = (sumSqForm k).eval _ at h3
    rwa [r9_eval, r9_eval] at h3
  rw [h2]

lemma glImage_blkGL_splitLat {k : ℕ} (γ : GL (Fin k) ℚ) (M : Submodule (𝓞 ℚ) (Fin k → ℚ)) :
    glImage (blkGL γ) (splitLat M) = splitLat (glImage γ M) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    show (blkGL γ).val *ᵥ w ∈ splitLat (glImage γ M)
    rw [blkGL_mulVec, mem_splitLat]
    simp only [spExt_castSucc, spExt_last]
    exact ⟨mulVec_mem_glImage hw.1, hw.2⟩
  · rintro ⟨hz1, m, hm⟩
    obtain ⟨u, hu, hu'⟩ := hz1
    refine ⟨spExt u m, ⟨by simpa using hu, m, by simp⟩, ?_⟩
    show (blkGL γ).val *ᵥ spExt u m = z
    rw [blkGL_mulVec]
    have h1 : γ.val *ᵥ u = fun i => z (Fin.castSucc i) := hu'
    have h2 : (fun i : Fin k => spExt u (m : ℚ) (Fin.castSucc i)) = u := by funext i; simp
    rw [h2, spExt_last, h1, ← hm]
    exact (spExt_eta z).symm

/-- $L' \perp \mathbb Z$ for $L' = \mathbb Z^k$ is $\mathbb Z^{k+1}$. -/
lemma splitLat_intVec {k : ℕ} :
    splitLat (intVec : Submodule (𝓞 ℚ) (Fin k → ℚ)) = intVec := by
  ext z
  rw [mem_splitLat, mem_intVec, mem_intVec]
  constructor
  · rintro ⟨h1, m, hm⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨(m : 𝓞 ℚ), by simp [hm]⟩
    · exact h1 j
  · intro h
    refine ⟨fun i => h _, ?_⟩
    obtain ⟨a, ha⟩ := h (Fin.last k)
    obtain ⟨m, hm⟩ : ∃ m : ℤ, ((m : ℤ) : 𝓞 ℚ) = a :=
      ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩
    exact ⟨m, by rw [← ha, ← hm]; simp⟩

/-- $\gamma\mathbb Z^k \perp \mathbb Z$ is isometric to $\mathbb Z^{k+1}$ whenever $\gamma \in O(I_k)$. -/
lemma isIsometric_splitLat_of_intVec {k : ℕ} {L' : Submodule (𝓞 ℚ) (Fin k → ℚ)}
    (h : IsIsometric (sumSqForm k) intVec L') : IsIsometric (sumSqForm (k + 1)) intVec (splitLat L') := by
  obtain ⟨γ, hγ, rfl⟩ := h
  refine ⟨blkGL γ, blkGL_mem_orth hγ, ?_⟩
  rw [← splitLat_intVec, glImage_blkGL_splitLat]

private lemma r9_eval_spExt_zero_one (k : ℕ) : (sumSqForm (k + 1)).eval (spExt (0 : Fin k → ℚ) 1) = 1 := by
  rw [r9_eval, r9_sum_succ]
  simp

/-- A nonzero vector of $\mathbb Q^n$ has $Q \ne 0$ for $Q = I_n$. -/
private lemma r9_eval_ne_zero {n : ℕ} {z : Fin n → ℚ} (hz : z ≠ 0) : (sumSqForm n).eval z ≠ 0 := by
  intro h
  rw [r9_eval] at h
  apply hz
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (z j))).mp h i (Finset.mem_univ i)
  simpa using this

/-- **Splitting off a vector of norm $1$** (O'Meara 1973, §106D, p. 330, "$L$ represents $1$, hence $L$ splits"; used
in 106:12 and 106:13). Let $L$ be a unimodular lattice on $V = I_{k+1}$ ($k + 1$ variables) containing a vector $x$ with
$Q(x) = 1$. Then there are an isometry $\sigma \in O(V)$ and a unimodular lattice $L'$ on $I_k$ with
$\sigma L = L' \perp \mathbb Z$ (`splitLat L'`: first $k$ coordinates in $L'$, last coordinate an integer); that is,
$L \cong \mathbb Zx \perp L'$ with $L'$ a unimodular lattice on $I_k$.

Proof: $\sigma$ is the symmetry $\tau_{e - x}$ ($e = $ the last unit vector) carrying $x$ to $e$ (or $1$ if $x = e$); then
$\sigma L$ is unimodular and contains $e$, so $B(y, e) \in \mathbb Z$ for $y \in \sigma L$, and
$L' = \{u : (u, 0) \in \sigma L\}$ is unimodular (as $B((u,0), y) = B(u, y_{\mathrm{init}})$ and
$(y_{\mathrm{init}}, 0) = y - y_{\mathrm{last}}e \in \sigma L$) and a lattice (global bounds). -/
@[kb "omeara1963" "§106D, p. 330 (a unimodular lattice representing 1 splits: L = Zx ⊥ L')"]
theorem unimodular_split_unit {k : ℕ} {L : Lat ℚ (k + 1)} (hL : IsUnimodularZ (sumSqForm (k + 1)) L.1)
    {x : Fin (k + 1) → ℚ} (hx : x ∈ L.1) (h1 : (sumSqForm (k + 1)).eval x = 1) :
    ∃ (σ : GL (Fin (k + 1)) ℚ) (L' : Lat ℚ k), σ ∈ orthGroup (sumSqForm (k + 1)) ℚ ∧
      IsUnimodularZ (sumSqForm k) L'.1 ∧ glImage σ L.1 = splitLat L'.1 := by
  set e : Fin (k + 1) → ℚ := spExt (0 : Fin k → ℚ) 1 with he_def
  have hee : (sumSqForm (k + 1)).eval e = 1 := r9_eval_spExt_zero_one k
  obtain ⟨σ, hσ, hσx⟩ : ∃ σ : GL (Fin (k + 1)) ℚ, σ ∈ orthGroup (sumSqForm (k + 1)) ℚ ∧ σ.val *ᵥ x = e := by
    by_cases hxe : e - x = 0
    · refine ⟨1, (orthGroup _ ℚ).one_mem, ?_⟩
      rw [sub_eq_zero] at hxe
      simp [hxe]
    · have hne : (sumSqForm (k + 1)).evalIn ℚ (e - x) ≠ 0 := r9_eval_ne_zero hxe
      exact ⟨(symm (sumSqForm (k + 1)) ℚ (e - x) : GL (Fin (k + 1)) ℚ), (symm _ ℚ (e - x)).2,
        symm_sub_apply (sumSqForm (k + 1)) ℚ (by
          change (sumSqForm (k + 1)).eval e = (sumSqForm (k + 1)).eval x
          rw [hee, h1]) hne⟩
  set L₁ : Submodule (𝓞 ℚ) (Fin (k + 1) → ℚ) := glImage σ L.1 with hL₁def
  have hL₁ : IsUnimodularZ (sumSqForm (k + 1)) L₁ := by
    unfold IsUnimodularZ
    rw [hL₁def, omearaDual_glImage _ hσ, show omearaDual (sumSqForm (k + 1)) L.1 = L.1 from hL]
  have hL₁lat : L₁.IsLattice ℚ := glImage_isLattice σ L.2
  have heL : e ∈ L₁ := ⟨x, hx, hσx⟩
  have hlast : ∀ y ∈ L₁, ∃ m : ℤ, y (Fin.last k) = m := by
    intro y hy
    obtain ⟨m, hm⟩ := uni_mem' _ hL₁ hy heL
    rw [he_def, bil_eta_right, r9_bil_zero_right] at hm
    exact ⟨m, by linarith⟩
  have hinit : ∀ y ∈ L₁, spExt (fun i => y (Fin.castSucc i)) 0 ∈ L₁ := by
    intro y hy
    obtain ⟨m, hm⟩ := hlast y hy
    have : spExt (fun i => y (Fin.castSucc i)) 0 = y - (m : ℚ) • e := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [he_def, hm]
      · simp [he_def]
    rw [this]
    exact L₁.sub_mem hy (intCast_smul_mem heL m)
  -- the lattice L'
  let L'sub : Submodule (𝓞 ℚ) (Fin k → ℚ) :=
    { carrier := {u | spExt u 0 ∈ L₁}
      add_mem' := fun {u v} hu hv => by
        have := spExt_add u v 0 0
        rw [add_zero] at this
        show spExt (u + v) 0 ∈ L₁
        rw [this]; exact L₁.add_mem hu hv
      zero_mem' := by
        show spExt (0 : Fin k → ℚ) 0 ∈ L₁
        have : spExt (0 : Fin k → ℚ) 0 = 0 := by funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
        rw [this]; exact L₁.zero_mem
      smul_mem' := fun c u hu => by
        obtain ⟨j, hj⟩ := exists_int_smul_eq c u
        show spExt (c • u) 0 ∈ L₁
        rw [hj]
        have := spExt_smul (j : ℚ) u 0
        rw [mul_zero] at this
        rw [this]
        exact intCast_smul_mem hu j }
  have hmemL' : ∀ u, u ∈ L'sub ↔ spExt u 0 ∈ L₁ := fun u => Iff.rfl
  have hL'lat : L'sub.IsLattice ℚ := by
    obtain ⟨d, hd0, hd1, hd2⟩ := exists_global_bounds hL₁lat
    refine isLattice_of_global_bounds hd0 (fun u hu => ?_) (fun u hu => ?_)
    · rw [hmemL']
      have hu' : spExt u 0 ∈ (intVec : Submodule (𝓞 ℚ) (Fin (k + 1) → ℚ)) := by
        rw [mem_intVec] at hu ⊢
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact ⟨0, by simp⟩
        · simpa using hu j
      have := hd1 _ hu'
      have e2 : spExt (d • u) 0 = d • spExt u 0 := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp [Pi.smul_apply]
      rw [e2]; exact this
    · have := hd2 _ ((hmemL' u).mp hu)
      rw [mem_intVec] at this ⊢
      intro i
      have := this (Fin.castSucc i)
      simpa [Pi.smul_apply] using this
  have hL'uni : IsUnimodularZ (sumSqForm k) L'sub := by
    unfold IsUnimodularZ
    ext x'
    constructor
    · intro hx'
      rw [hmemL', ← hL₁]
      intro y hy
      have hy' : (fun i => y (Fin.castSucc i)) ∈ L'sub := hinit y hy
      obtain ⟨m, hm⟩ := hx' _ hy'
      refine ⟨m, ?_⟩
      rw [bil_eta_left]
      linarith
    · intro hx' v hv
      obtain ⟨m, hm⟩ := uni_mem' _ hL₁ hx' hv
      refine ⟨m, ?_⟩
      have := bil_spExt x' v 0 0
      rw [mul_zero, mul_zero, add_zero] at this
      rw [← this]
      exact hm
  refine ⟨σ, ⟨L'sub, hL'lat⟩, hσ, hL'uni, ?_⟩
  ext z
  rw [mem_splitLat]
  constructor
  · intro hz
    exact ⟨hinit z hz, hlast z hz⟩
  · rintro ⟨hz1, m, hm⟩
    have hz1' : spExt (fun i => z (Fin.castSucc i)) 0 ∈ L₁ := hz1
    have : z = spExt (fun i => z (Fin.castSucc i)) 0 + (m : ℚ) • e := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [he_def, hm]
      · simp [he_def]
    rw [this]
    exact L₁.add_mem hz1' (intCast_smul_mem heL m)

/-- **A unimodular lattice on $I_{k+1}$ representing $1$ is isometric to $\mathbb Z^{k+1}$ as soon as all unimodular
lattices on $I_k$ are isometric to $\mathbb Z^k$** (O'Meara 1973, §106D–F, pp. 330, 333, the step "$L$ splits, hence
$L \cong I_n$ by 106:10"): from `unimodular_split_unit` and the block-diagonal isometry. -/
theorem unimodular_split_isIsometric {k : ℕ}
    (hk : ∀ L' : Lat ℚ k, IsUnimodularZ (sumSqForm k) L'.1 → IsIsometric (sumSqForm k) intVec L'.1)
    {L : Lat ℚ (k + 1)} (hL : IsUnimodularZ (sumSqForm (k + 1)) L.1)
    {x : Fin (k + 1) → ℚ} (hx : x ∈ L.1) (h1 : (sumSqForm (k + 1)).eval x = 1) :
    IsIsometric (sumSqForm (k + 1)) intVec L.1 := by
  obtain ⟨σ, L', hσ, hL', hσL⟩ := unimodular_split_unit hL hx h1
  have h2 := isIsometric_splitLat_of_intVec (hk L' hL')
  rw [← hσL] at h2
  refine IsIsometric.trans _ h2 ⟨σ⁻¹, (orthGroup _ ℚ).inv_mem hσ, ?_⟩
  rw [← glImage_mul, inv_mul_cancel, glImage_one]

end Split

/-! ### Helpers on adjacent lattices -/

section Adjacent

private lemma r9_nm_two : nm (2 : 𝓞 ℚ) = 2 := by
  have h : (2 : 𝓞 ℚ) = ((2 : ℕ) : 𝓞 ℚ) := by norm_num
  rw [h, nm_natCast, NumberField.RingOfIntegers.rank]
  simp

/-- Two adjacent lattices differ: there is $y \in L - K$. -/
private lemma r9_exists_out {n : ℕ} {Q : QuadForm ℚ n} {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (h : Nbr.IsNbrL Q 2 L K) : ∃ y ∈ L, y ∉ K := by
  by_contra hcon
  have hle : L ≤ K := fun x hx => by
    by_contra hxK
    exact hcon ⟨x, hx, hxK⟩
  have h1 := h.index_left
  rw [r9_nm_two] at h1
  have e : (L ⊓ K).toAddSubgroup = L.toAddSubgroup ⊓ K.toAddSubgroup := rfl
  have h2 : (L ⊓ K).toAddSubgroup.relIndex L.toAddSubgroup = 2 := by
    rw [e, AddSubgroup.inf_relIndex_left, h1]
  rw [inf_eq_left.mpr hle, AddSubgroup.relIndex_self] at h2
  omega

private lemma r9_two_smul_mem {n : ℕ} {Q : QuadForm ℚ n} {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hadj : Nbr.IsNbrL Q 2 L K) {y : Fin n → ℚ} (hyL : y ∈ L) : (2 : ℚ) • y ∈ K := by
  have h := hadj.smul_right y hyL
  have e : algebraMap (𝓞 ℚ) ℚ 2 = 2 := map_ofNat _ 2
  rwa [e] at h

/-- A neighbour of a lattice is a lattice. -/
private lemma r9_isLattice_nbr {n : ℕ} {Q : QuadForm ℚ n} {M M' : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hM : M.IsLattice ℚ) (h : Nbr.IsNbrL Q 2 M M') : M'.IsLattice ℚ := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hM
  have hπ : (2 : 𝓞 ℚ) ≠ 0 := two_ne_zero
  refine isLattice_of_global_bounds (d := 2 * d) (mul_ne_zero hπ hd) (fun z hz => ?_) (fun z hz => ?_)
  · rw [mul_smul, ← algebraMap_smul ℚ]
    exact h.smul_right _ (h1 z hz)
  · rw [mul_comm, mul_smul, ← algebraMap_smul ℚ (2 : 𝓞 ℚ)]
    exact h2 _ (h.smul_left _ hz)

/-- Transport of adjacency along an isometry: if $X = \sigma X_0$ and the unimodular $Y$ is adjacent to $X$, then
$Y_0 = \sigma^{-1}Y$ is a unimodular lattice adjacent to $X_0$ and isometric to $Y$. -/
private lemma r9_transport {n : ℕ} {X0 X Y : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hX : IsIsometric (sumSqForm n) X0 X) (hY : IsUnimodularZ (sumSqForm n) Y)
    (hadj : Nbr.IsNbrL (sumSqForm n) 2 X Y) :
    ∃ Y0 : Submodule (𝓞 ℚ) (Fin n → ℚ), IsUnimodularZ (sumSqForm n) Y0 ∧
      Nbr.IsNbrL (sumSqForm n) 2 X0 Y0 ∧ IsIsometric (sumSqForm n) Y0 Y := by
  obtain ⟨σ, hσ, hσX⟩ := hX
  have hσi : (σ⁻¹ : GL (Fin n) ℚ) ∈ orthGroup (sumSqForm n) ℚ := (orthGroup _ ℚ).inv_mem hσ
  have hX' : glImage (σ⁻¹ : GL (Fin n) ℚ) X = X0 := by
    rw [← hσX, ← glImage_mul, inv_mul_cancel, glImage_one]
  refine ⟨glImage (σ⁻¹ : GL (Fin n) ℚ) Y, ?_, ?_, ⟨σ, hσ, ?_⟩⟩
  · unfold IsUnimodularZ
    rw [omearaDual_glImage _ hσi, show omearaDual (sumSqForm n) Y = Y from hY]
  · have := hadj.glImage hσi
    rwa [hX'] at this
  · rw [← glImage_mul, mul_inv_cancel, glImage_one]

variable {n : ℕ} (Q : QuadForm ℚ n)

/-- **Key dichotomy for a vector of norm $1$ near an adjacent lattice** (the common core of the cases of 106:12 and of
the key step of 106:10, O'Meara 1973, pp. 330, 333–334). Let $K_0, K$ be unimodular and adjacent, $y \in K - K_0$, and
let $w$ satisfy $Q(w) = 1$ and $y - w \in K_0$. Then $B(y, w) \in \tfrac12\mathbb Z$ and either $B(y, w) \in \mathbb Z$, in
which case $w \in K$ (by 106:6), or $B(y, w) \in \tfrac12 + \mathbb Z$, in which case the symmetry $\tau_w$ carries $K$ onto
$K_0$ (106:9). So either $K$ contains a vector of norm $1$, or $K$ is isometric to $K_0$. Auxiliary (not in the book). -/
theorem key_norm_one {K0 K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK0 : IsUnimodularZ Q K0) (hK : IsUnimodularZ Q K)
    (hadj : Nbr.IsNbrL Q 2 K K0) {y w : Fin n → ℚ} (hyK : y ∈ K) (hyK0 : y ∉ K0) (hw : Q.eval w = 1)
    (hyw : y - w ∈ K0) : w ∈ K ∨ IsIsometric Q K K0 := by
  obtain ⟨m1, hm1⟩ := uni_Q_int Q hK hyK
  obtain ⟨m2, hm2⟩ := uni_Q_int Q hK0 hyw
  -- bil y w = m1 - m2 + 1
  have hsum : Q.eval y = Q.eval (y - w) + Q.eval w + bil Q (y - w) w := by
    have := ClassFin.eval_add Q (y - w) w
    rwa [sub_add_cancel] at this
  have hbww : bil Q w w = 2 := by rw [bil_self_eq, hw]; norm_num
  have hbyw : bil Q y w = ((m1 - m2 + 1 : ℤ) : ℚ) := by
    have h1 : bil Q (y - w) w = bil Q y w - bil Q w w := bil_sub_left' Q y w w
    push_cast
    rw [h1, hbww] at hsum
    rw [hm1, hm2, hw] at hsum
    linarith
  rcases Int.even_or_odd' (m1 - m2 + 1) with ⟨m, hm | hm⟩
  · -- B(y, w) = m ∈ ℤ : w ∈ K
    left
    have hu : y - w ∈ K ⊓ K0 := by
      refine ((omeara106_6 Q hK0 hK hadj hyK hyK0).2.2.2 (y - w)).mpr ⟨hyw, m1 - m, ?_⟩
      have h1 : bil Q (y - w) y = bil Q y y - bil Q w y := by
        rw [bil_sub_left']
      rw [h1, bil_self_eq, bil_comm Q w y, hbyw, hm]
      rw [hm1]
      push_cast
      ring
    have : w = y - (y - w) := by abel
    rw [this]
    exact K.sub_mem hyK (Submodule.mem_inf.mp hu).1
  · -- B(y, w) ∈ 1/2 + ℤ
    right
    obtain ⟨-, hiso⟩ := omeara106_9 Q hK0 hK hadj hyK hyK0 (show y = w + (y - w) by abel) hw hyw
      ⟨m, by rw [hbyw, hm]; push_cast; ring⟩
    exact hiso

end Adjacent

/-! ### Integer description of $E$ for $n = 8$ and a covering lemma -/

section Covering

/-- The integer criterion for membership of $f/4$ in $E$ ($n = 8$), from 106:11: all $f_i$ even, all differences
divisible by $4$, and $8 \mid \sum f_i$. Auxiliary. -/
def Ecrit (f : Fin 8 → ℤ) : Prop :=
  (∀ i, 2 ∣ f i) ∧ (∀ i j, 4 ∣ f i - f j) ∧ 8 ∣ ∑ i, f i

lemma mem_E8_iff_crit (f : Fin 8 → ℤ) : (fun i => (f i : ℚ) / 4) ∈ omearaE 8 ↔ Ecrit f := by
  rw [omeara106_11 (by norm_num : 4 ∣ 8) (by norm_num : 0 < 8)]
  unfold Ecrit
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have : (f i : ℚ) = 2 * m := by linarith
      exact_mod_cast this
    · rintro ⟨m, hm⟩
      exact ⟨m, by rw [hm]; push_cast; ring⟩
  · refine forall_congr' fun i => forall_congr' fun j => ?_
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have : (f i : ℚ) - f j = 4 * m := by linarith
      exact_mod_cast this
    · rintro ⟨m, hm⟩
      exact ⟨m, by
        have : (f i : ℚ) - f j = 4 * m := by exact_mod_cast hm
        linarith⟩
  · have e : ∑ i, (f i : ℚ) / 4 = ((∑ i, f i : ℤ) : ℚ) / 4 := by
      rw [← Finset.sum_div]; push_cast; rfl
    show (∃ m : ℤ, ∑ i, (f i : ℚ) / 4 = 2 * m) ↔ _
    rw [e]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have : ((∑ i, f i : ℤ) : ℚ) = 8 * m := by linarith
      exact_mod_cast this
    · rintro ⟨m, hm⟩
      exact ⟨m, by rw [hm]; push_cast; ring⟩

private lemma r9_P_term (c d : ℤ) (hd : d % 2 = 1) (h4 : 4 ∣ c - d) :
    ∃ e t : ℤ, c = d + 4 * e ∧ c ^ 2 = d ^ 2 + 8 * e + 16 * t := by
  obtain ⟨e, he⟩ := h4
  obtain ⟨s, hs⟩ : ∃ s, d = 2 * s + 1 := ⟨d / 2, by omega⟩
  have hc : c = d + 4 * e := by omega
  refine ⟨e, s * e + e ^ 2, hc, ?_⟩
  rw [hc, hs]
  ring

private lemma r9_sq_mod4 (k : ℤ) : k ^ 2 % 4 = if k % 2 = 1 then 1 else 0 := by
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    have h1 : ¬ (2 * j) % 2 = 1 := by omega
    simp only [h1, ite_false]
    have : (2 * j) ^ 2 = 4 * j ^ 2 := by ring
    rw [this]
    exact Int.mul_emod_right 4 _
  · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    simp only [h, ite_true]
    have : (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by ring
    rw [this]
    generalize j ^ 2 + j = x
    omega

private lemma r9_sq_mod16 (c : ℤ) (hc : 2 ∣ c) : c ^ 2 % 16 = if c % 4 = 2 then 4 else 0 := by
  obtain ⟨k, rfl⟩ := hc
  have h := r9_sq_mod4 k
  have e : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
  rw [e]
  generalize k ^ 2 = x at h ⊢
  split_ifs at h ⊢ <;> omega

/-- Odd case of the covering lemma: all $c_i$ odd. -/
private lemma nt8_odd (c : Fin 8 → ℤ) (hodd : ∀ i, c i % 2 = 1) (hQ : 16 ∣ ∑ i, c i ^ 2) :
    ∃ d : Fin 8 → ℤ, ∑ i, d i ^ 2 = 16 ∧ Ecrit (fun i => c i - d i) := by
  let d : Fin 8 → ℤ := fun i =>
    if c i % 4 = 1 then (if i = 0 then -3 else 1) else (if i = 0 then 3 else -1)
  have hd1 : ∀ i, d i % 2 = 1 := by
    intro i; have := hodd i; simp only [d]; split_ifs <;> omega
  have hd4 : ∀ i, 4 ∣ c i - d i := by
    intro i; have := hodd i; simp only [d]; split_ifs <;> omega
  have hd2 : ∀ i, d i ^ 2 = if i = 0 then 9 else 1 := by
    intro i; simp only [d]; split_ifs <;> norm_num
  have hsum : ∑ i, d i ^ 2 = 16 := by
    rw [Finset.sum_congr rfl fun i _ => hd2 i]
    simp [Fin.sum_univ_succ]
  choose e t he ht using fun i => r9_P_term (c i) (d i) (hd1 i) (hd4 i)
  have hs : ∑ i, c i ^ 2 = ∑ i, d i ^ 2 + 8 * ∑ i, e i + 16 * ∑ i, t i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => ht i
  have hev : 2 ∣ ∑ i, e i := by
    rw [hs, hsum] at hQ
    omega
  refine ⟨d, hsum, ?_⟩
  unfold Ecrit
  refine ⟨fun i => dvd_trans (by norm_num : (2 : ℤ) ∣ 4) (hd4 i), fun i j => dvd_sub (hd4 i) (hd4 j), ?_⟩
  have : ∑ i, (c i - d i) = 4 * ∑ i, e i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by have := he i; omega
  rw [this]
  obtain ⟨m, hm⟩ := hev
  rw [hm]
  exact ⟨m, by ring⟩

/-- Even case of the covering lemma, all $c_i$ congruent modulo $4$. -/
private lemma nt8_even_flat (c : Fin 8 → ℤ) (hev : ∀ i, 2 ∣ c i) (hflat : ∀ i j, 4 ∣ c i - c j)
    (h4 : 4 ∣ ∑ i, c i) (hn : ¬ Ecrit c) :
    ∃ d : Fin 8 → ℤ, ∑ i, d i ^ 2 = 16 ∧ Ecrit (fun i => c i - d i) := by
  have h8 : ¬ 8 ∣ ∑ i, c i := fun h => hn ⟨hev, hflat, h⟩
  let d : Fin 8 → ℤ := fun i => if i = 0 then 4 else 0
  have hsum2 : ∑ i, d i ^ 2 = 16 := by simp [d]
  have hsumd : ∑ i, d i = 4 := by simp [d]
  refine ⟨d, hsum2, ?_⟩
  unfold Ecrit
  refine ⟨fun i => ?_, fun i j => ?_, ?_⟩
  · have := hev i; simp only [d]; split_ifs <;> omega
  · have := hflat i j; simp only [d]; split_ifs <;> omega
  · rw [Finset.sum_sub_distrib, hsumd]; omega

/-- Even case of the covering lemma, the $c_i$ not all congruent modulo $4$: exactly four are $\equiv 2$. -/
private lemma nt8_even_mixed (c : Fin 8 → ℤ) (hev : ∀ i, 2 ∣ c i) (hflat : ¬ ∀ i j, 4 ∣ c i - c j)
    (h4 : 4 ∣ ∑ i, c i) (hQ : 16 ∣ ∑ i, c i ^ 2) :
    ∃ d : Fin 8 → ℤ, ∑ i, d i ^ 2 = 16 ∧ Ecrit (fun i => c i - d i) := by
  classical
  set S : Finset (Fin 8) := Finset.univ.filter fun i => c i % 4 = 2 with hSdef
  have hmem : ∀ i, i ∈ S ↔ c i % 4 = 2 := fun i => by simp [hSdef]
  have hcard : S.card = 4 := by
    have hmod : (∑ i, c i ^ 2) % 16 = (4 * (S.card : ℤ)) % 16 := by
      rw [Finset.sum_int_mod]
      have : ∀ i ∈ (Finset.univ : Finset (Fin 8)), c i ^ 2 % 16 = if c i % 4 = 2 then 4 else 0 :=
        fun i _ => r9_sq_mod16 (c i) (hev i)
      rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      ring
    have h0 : (4 * (S.card : ℤ)) % 16 = 0 := by rw [← hmod]; omega
    have hne : S.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      apply hflat
      intro i j
      have hi : ¬ c i % 4 = 2 := fun h => by
        have := (hmem i).mpr h; rw [hcon] at this; simp at this
      have hj : ¬ c j % 4 = 2 := fun h => by
        have := (hmem j).mpr h; rw [hcon] at this; simp at this
      have := hev i; have := hev j; omega
    have hlt : S.card < 8 := by
      have : S ⊂ Finset.univ := by
        rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
        by_contra hcon
        push Not at hcon
        apply hflat
        intro i j
        have hi := (hmem i).mp (hcon i (Finset.mem_univ i))
        have hj := (hmem j).mp (hcon j (Finset.mem_univ j))
        omega
      simpa using Finset.card_lt_card this
    have hpos : 0 < S.card := Finset.card_pos.mpr hne
    omega
  obtain ⟨j0, hj0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb, hb8⟩ : ∃ b : ℤ, (b = 0 ∨ b = 4) ∧ 8 ∣ (∑ i, c i) - (8 - b) := by
    by_cases h8 : (∑ i, c i) % 8 = 0
    · exact ⟨0, Or.inl rfl, by omega⟩
    · exact ⟨4, Or.inr rfl, by omega⟩
  let d : Fin 8 → ℤ := fun i => (if i ∈ S then 2 else 0) - (if i = j0 then b else 0)
  have hd2 : ∀ i, d i ^ 2 = if i ∈ S then 4 else 0 := by
    intro i
    simp only [d]
    by_cases hi : i ∈ S
    · by_cases hij : i = j0
      · subst hij; rcases hb with rfl | rfl <;> norm_num [hi]
      · norm_num [hi, hij]
    · have : i ≠ j0 := fun h => hi (h ▸ hj0)
      simp [hi, this]
  have hd4 : ∀ i, 4 ∣ c i - d i := by
    intro i
    have h1 := hev i
    have h2 := hmem i
    simp only [d]
    by_cases hi : i ∈ S
    · have := h2.mp hi
      by_cases hij : i = j0
      · subst hij; rcases hb with rfl | rfl <;> simp [hi] <;> omega
      · simp [hi, hij]; omega
    · have : i ≠ j0 := fun h => hi (h ▸ hj0)
      have h3 : ¬ c i % 4 = 2 := fun h => hi (h2.mpr h)
      simp [hi, this]; omega
  have hsum2 : ∑ i, d i ^ 2 = 16 := by
    rw [Finset.sum_congr rfl fun i _ => hd2 i, ← Finset.sum_filter]
    have : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
    rw [this, Finset.sum_const, hcard]
    norm_num
  have hsumd : ∑ i, d i = 8 - b := by
    simp only [d]
    rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
    have : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
    rw [this, Finset.sum_const, hcard]
    simp
  refine ⟨d, hsum2, ?_⟩
  unfold Ecrit
  refine ⟨fun i => dvd_trans (by norm_num : (2 : ℤ) ∣ 4) (hd4 i), fun i j => dvd_sub (hd4 i) (hd4 j), ?_⟩
  rw [Finset.sum_sub_distrib, hsumd]
  exact hb8

/-- **Covering lemma for $E_8$** (the combinatorial core of O'Meara's cases 1)–4) in 106:12, p. 333–334). Let
$c \in \mathbb Z^8$ with all $c_i$ of the same parity (`hpar`), $4 \mid \sum c_i$ (`h4`; with `hpar` this says
$2\cdot\tfrac14c \in E$), $16 \mid \sum c_i^2$ (`hQ`; $Q(\tfrac14c) \in \mathbb Z$) and $\tfrac14c \notin E$ (`hn`).
Then there is $d \in \mathbb Z^8$ with $\sum d_i^2 = 16$ (so $Q(\tfrac14d) = 1$) and $\tfrac14(c - d) \in E$. Auxiliary:
it replaces the book's case-by-case reduction by one integer computation. -/
theorem nt8 (c : Fin 8 → ℤ) (hpar : ∀ i j, 2 ∣ c i - c j) (h4 : 4 ∣ ∑ i, c i) (hQ : 16 ∣ ∑ i, c i ^ 2)
    (hn : ¬ Ecrit c) : ∃ d : Fin 8 → ℤ, ∑ i, d i ^ 2 = 16 ∧ Ecrit (fun i => c i - d i) := by
  by_cases h0 : c 0 % 2 = 1
  · exact nt8_odd c (fun i => by have := hpar i 0; omega) hQ
  · have hev : ∀ i, 2 ∣ c i := fun i => by have := hpar i 0; omega
    by_cases hflat : ∀ i j, 4 ∣ c i - c j
    · exact nt8_even_flat c hev hflat h4 hn
    · exact nt8_even_mixed c hev hflat h4 hQ

/-- **A vector of norm $1$ near each vector of $\tfrac12E - E$ of integral norm** ($n = 8$): if $2z \in E$, $z \notin E$
and $Q(z) \in \mathbb Z$ then there is $w$ with $Q(w) = 1$ and $z - w \in E$ (O'Meara's cases 1)–4) of 106:12,
pp. 333–334, which reduce $z$ modulo $L \cap E$ to one of the shapes $\tfrac12(\pm x_a \pm x_b \pm x_c \pm x_d)$,
$\tfrac14(a x_0 + x_1 + \dots + x_7)$, etc.; here the vector $w$ is written down by `nt8`). Auxiliary. -/
theorem exists_unit_vec_E {z : Fin 8 → ℚ} (h2 : (2 : ℚ) • z ∈ omearaE 8) (hz : z ∉ omearaE 8)
    (hQ : ∃ m : ℤ, (sumSqForm 8).eval z = m) :
    ∃ w : Fin 8 → ℚ, (sumSqForm 8).eval w = 1 ∧ z - w ∈ omearaE 8 := by
  obtain ⟨p1, p2, ⟨m, hm⟩⟩ := (omeara106_11 (by norm_num : 4 ∣ 8) (by norm_num : 0 < 8) _).mp h2
  choose c hc using p1
  have hzc : z = fun i => (c i : ℚ) / 4 := by
    funext i
    have := hc i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hzc' : ∀ i, z i = (c i : ℚ) / 4 := fun i => congrFun hzc i
  have hpar : ∀ i j, 2 ∣ c i - c j := by
    intro i j
    obtain ⟨k, hk⟩ := p2 i j
    simp only [Pi.smul_apply, smul_eq_mul, hzc'] at hk
    refine ⟨k, ?_⟩
    have : ((c i - c j : ℤ) : ℚ) = 2 * k := by push_cast; linarith
    exact_mod_cast this
  have h4 : 4 ∣ ∑ i, c i := by
    refine ⟨m, ?_⟩
    have : ((∑ i, c i : ℤ) : ℚ) = 4 * m := by
      push_cast
      have e : ∑ i, ((2 : ℚ) • z) i = ∑ i, (c i : ℚ) / 2 :=
        Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul, hzc']; ring
      rw [e, ← Finset.sum_div] at hm
      linarith
    exact_mod_cast this
  have hQ' : 16 ∣ ∑ i, c i ^ 2 := by
    obtain ⟨q, hq⟩ := hQ
    rw [r9_eval] at hq
    refine ⟨q, ?_⟩
    have : ((∑ i, c i ^ 2 : ℤ) : ℚ) = 16 * q := by
      push_cast
      rw [← hq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hzc' i]; ring
    exact_mod_cast this
  have hn : ¬ Ecrit c := fun h => hz (by rw [hzc]; exact (mem_E8_iff_crit c).mpr h)
  obtain ⟨d, hd1, hd2⟩ := nt8 c hpar h4 hQ' hn
  refine ⟨fun i => (d i : ℚ) / 4, ?_, ?_⟩
  · rw [r9_eval]
    have : ∑ i, ((d i : ℚ) / 4) ^ 2 = ((∑ i, d i ^ 2 : ℤ) : ℚ) / 16 := by
      push_cast
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hd1]
    norm_num
  · have : z - (fun i => (d i : ℚ) / 4) = fun i => ((c i - d i : ℤ) : ℚ) / 4 := by
      funext i
      simp only [Pi.sub_apply, hzc' i]
      push_cast
      ring
    rw [this]
    exact (mem_E8_iff_crit _).mpr hd2

end Covering

/-! ### 106:12 -/

section Rank8

/-- A unimodular lattice on $I_8$ containing a vector of norm $1$ is isometric to $\mathbb Z^8$ (splitting off the
vector and 106:10 for $n = 7$, `omeara106_10_uncond`). -/
theorem isIsometric_of_norm_one_rank8 {K : Submodule (𝓞 ℚ) (Fin 8 → ℚ)} (hlat : K.IsLattice ℚ)
    (hK : IsUnimodularZ (sumSqForm 8) K) {w : Fin 8 → ℚ} (hw : w ∈ K) (h1 : (sumSqForm 8).eval w = 1) :
    IsIsometric (sumSqForm 8) intVec K :=
  unimodular_split_isIsometric (k := 7) (fun L' hL' => omeara106_10_uncond (by norm_num) (by norm_num) hL')
    (L := ⟨K, hlat⟩) hK hw h1

/-- **Proposition 106:12** (O'Meara 1973, §106E, p. 333). Let $n = 8$, $V = I_8$, $E$ = `omearaE 8`, $D = \mathbb Z^8$
(`intVec`). If $L$ is a unimodular lattice adjacent to $E$ (`Nbr.IsNbrL (sumSqForm 8) 2 L (omearaE 8)`), then $L$ is
in the class of $D$ or in the class of $E$ (`IsIsometric`, isometries of the full orthogonal group $O(V)$ as in the
book's "cls").

*Proof (different bookkeeping from the book's four cases).* Take $z \in L - E$; then $2z \in E$ and $Q(z) \in \mathbb Z$.
By the covering lemma `exists_unit_vec_E` (which packages O'Meara's cases 1)–4): reduction of $z$ modulo $L \cap E$ by
106:8) there is $w$ with $Q(w) = 1$ and $z - w \in E$. Then `key_norm_one` (106:6 and 106:9) shows that either
$w \in L$, so $L$ represents $1$, splits off $\mathbb Zw$ and is isometric to $D$ by 106:10 for $n = 7$
(`isIsometric_of_norm_one_rank8`), or $\tau_wL = E$ (106:9), so $L \cong E$. -/
@[kb "omeara1963" "§106E, 106:12, p. 333"]
theorem omeara106_12 {L : Submodule (𝓞 ℚ) (Fin 8 → ℚ)} (hL : IsUnimodularZ (sumSqForm 8) L)
    (hadj : Nbr.IsNbrL (sumSqForm 8) 2 L (omearaE 8)) :
    IsIsometric (sumSqForm 8) intVec L ∨ IsIsometric (sumSqForm 8) (omearaE 8) L := by
  obtain ⟨hE, -, hEadj⟩ := omeara106_r29_adjacent (n := 8) (by norm_num) le_rfl
  have hElat : (omearaE 8).IsLattice ℚ := r9_isLattice_nbr intVec_isLattice hEadj.symm
  have hLlat : L.IsLattice ℚ := r9_isLattice_nbr hElat hadj.symm
  obtain ⟨z, hzL, hzE⟩ := r9_exists_out hadj
  have h2 : (2 : ℚ) • z ∈ omearaE 8 := r9_two_smul_mem hadj hzL
  obtain ⟨w, hw1, hzw⟩ := exists_unit_vec_E h2 hzE (uni_Q_int _ hL hzL)
  rcases key_norm_one (sumSqForm 8) hE hL hadj hzL hzE hw1 hzw with hwL | hiso
  · exact Or.inl (isIsometric_of_norm_one_rank8 hLlat hL hwL hw1)
  · exact Or.inr hiso.symm

private lemma r9_mem_range {q : ℚ} : q ∈ (algebraMap (𝓞 ℚ) ℚ).range ↔ ∃ m : ℤ, q = m := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, ((m : ℤ) : 𝓞 ℚ) = a :=
      ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩
    exact ⟨m, by simp⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(m : 𝓞 ℚ), by simp⟩

private lemma r9_D_coord {n : ℕ} {x : Fin n → ℚ} :
    x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ ∀ i, ∃ m : ℤ, x i = m := by
  rw [mem_intVec]
  exact forall_congr' fun i => r9_mem_range

private lemma r9_diag {n : ℕ} (ε : Fin n → ℚ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∃ σ : GL (Fin n) ℚ, σ ∈ orthGroup (sumSqForm n) ℚ ∧ ∀ x i, (σ.val *ᵥ x) i = ε i * x i := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with h | h <;> simp [h]
  have hMM : Matrix.diagonal ε * Matrix.diagonal ε = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hε2 i
  refine ⟨⟨Matrix.diagonal ε, Matrix.diagonal ε, hMM, hMM⟩, ?_, ?_⟩
  · apply mem_orthGroup_of_eval
    intro z
    show (sumSqForm n).eval ((Matrix.diagonal ε) *ᵥ z) = (sumSqForm n).eval z
    rw [r9_eval, r9_eval]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_diagonal]
    calc (ε i * z i) ^ 2 = (ε i * ε i) * z i ^ 2 := by ring
      _ = z i ^ 2 := by rw [hε2 i, one_mul]
  · intro x i
    exact Matrix.mulVec_diagonal ε x i

private lemma r9_diag_D {n : ℕ} {σ : GL (Fin n) ℚ} (ε : Fin n → ℚ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hσ : ∀ x i, (σ.val *ᵥ x) i = ε i * x i) :
    glImage σ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) = intVec := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with h | h <;> simp [h]
  have hiff : ∀ x i, (∃ m : ℤ, (σ.val *ᵥ x) i = m) ↔ ∃ m : ℤ, x i = m := fun x i => by
    rw [hσ]
    rcases hε i with h | h <;> rw [h]
    · simp
    · constructor
      · rintro ⟨m, hm⟩
        exact ⟨-m, by push_cast; linarith⟩
      · rintro ⟨m, hm⟩
        exact ⟨-m, by push_cast; linarith⟩
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact r9_D_coord.mpr fun i => (hiff z i).mpr (r9_D_coord.mp hz i)
  · intro hx
    refine ⟨σ.val *ᵥ x, r9_D_coord.mpr fun i => (hiff x i).mpr (r9_D_coord.mp hx i), ?_⟩
    show σ.val *ᵥ (σ.val *ᵥ x) = x
    funext i
    rw [hσ, hσ, ← mul_assoc, hε2 i, one_mul]

/-- **A unimodular lattice adjacent to $D$ containing $y$ with all $2y_i$ odd is isometric to $E$** (the tail of
O'Meara's argument for 106.r30, pp. 332–333, without the determinant bookkeeping): modulo $2D \subseteq K \cap D$ one may
replace $y$ by $\tfrac12(\pm x_0 \pm \dots \pm x_7)$; the sign change $\sigma$ with $\sigma y_E = y$ preserves $D$, and
$\sigma E = K$ by 106:8a. Auxiliary. -/
theorem isIsometric_E_of_all_odd {K : Submodule (𝓞 ℚ) (Fin 8 → ℚ)} (hK : IsUnimodularZ (sumSqForm 8) K)
    (hadj : Nbr.IsNbrL (sumSqForm 8) 2 K intVec) {y : Fin 8 → ℚ} (hyK : y ∈ K)
    (hodd : ∀ i, ∃ a : ℤ, 2 * y i = a ∧ a % 2 = 1) : IsIsometric (sumSqForm 8) (omearaE 8) K := by
  have hD : IsUnimodularZ (sumSqForm 8) (intVec : Submodule (𝓞 ℚ) (Fin 8 → ℚ)) := adj_D_unimodular
  choose a ha hao using hodd
  have hsign : ∀ i, ∃ s : ℚ, ∃ d : ℤ, (s = 1 ∨ s = -1) ∧ y i = s / 2 + 2 * d := by
    intro i
    by_cases h : a i % 4 = 1
    · refine ⟨1, a i / 4, Or.inl rfl, ?_⟩
      have h' : a i = 4 * (a i / 4) + 1 := by omega
      have h'' : (a i : ℚ) = 4 * ((a i / 4 : ℤ) : ℚ) + 1 := by exact_mod_cast h'
      linarith [ha i]
    · refine ⟨-1, a i / 4 + 1, Or.inr rfl, ?_⟩
      have h0 := hao i
      have h' : a i = 4 * (a i / 4 + 1) - 1 := by omega
      have h'' : (a i : ℚ) = 4 * ((a i / 4 + 1 : ℤ) : ℚ) - 1 := by exact_mod_cast h'
      linarith [ha i]
  choose ε d hε hd using hsign
  obtain ⟨σ, hσO, hσx⟩ := r9_diag ε hε
  have hσD := r9_diag_D ε hε hσx
  obtain ⟨hEu, hyE, hEadj⟩ := omeara106_r29_adjacent (n := 8) (by norm_num) le_rfl
  have hσEuni : IsUnimodularZ (sumSqForm 8) (glImage σ (omearaE 8)) := by
    unfold IsUnimodularZ
    rw [omearaDual_glImage _ hσO, show omearaDual (sumSqForm 8) (omearaE 8) = omearaE 8 from hEu]
  have hσEadj : Nbr.IsNbrL (sumSqForm 8) 2 (glImage σ (omearaE 8)) intVec := by
    have := hEadj.glImage hσO
    rwa [hσD] at this
  obtain ⟨y'', hy''⟩ : ∃ y'' : Fin 8 → ℚ, y'' = fun i => ε i / 2 := ⟨_, rfl⟩
  have hyσ : y'' = σ.val *ᵥ omearaEHalf 8 := by
    rw [hy'']
    funext i
    rw [hσx]
    simp only [omearaEHalf]
    ring
  have hy''σE : y'' ∈ glImage σ (omearaE 8) := by
    rw [hyσ]
    exact mulVec_mem_glImage hyE
  have hy''K : y'' ∈ K := by
    have hdD : (fun i => (d i : ℚ)) ∈ (intVec : Submodule (𝓞 ℚ) (Fin 8 → ℚ)) :=
      r9_D_coord.mpr fun i => ⟨d i, rfl⟩
    have h2d := hadj.smul_left _ hdD
    have e2 : algebraMap (𝓞 ℚ) ℚ 2 = 2 := map_ofNat _ 2
    rw [e2] at h2d
    have : y'' = y - (2 : ℚ) • (fun i => (d i : ℚ)) := by
      rw [hy'']
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hd i]
    rw [this]
    exact K.sub_mem hyK h2d
  have hy''D : y'' ∉ (intVec : Submodule (𝓞 ℚ) (Fin 8 → ℚ)) := fun h => by
    obtain ⟨m, hm⟩ := r9_D_coord.mp h 0
    rw [hy''] at hm
    rcases hε 0 with h1 | h1 <;> simp only [h1] at hm
    · have h3 : (2 : ℚ) * m = 1 := by linarith
      have h4' : 2 * m = 1 := by exact_mod_cast h3
      omega
    · have h3 : (2 : ℚ) * m = -1 := by linarith
      have h4' : 2 * m = -1 := by exact_mod_cast h3
      omega
  have heq : glImage σ (omearaE 8) = K :=
    (omeara106_8a (sumSqForm 8) hD hσEuni hK hσEadj hadj hy''σE hy''D hy''K hy''D).mpr
      ⟨by rw [sub_self]; exact Submodule.zero_mem _, uni_mem' (sumSqForm 8) hK hy''K hy''K⟩
  exact ⟨σ, hσO, heq⟩

/-- **A unimodular lattice adjacent to $\mathbb Z^8$ is isometric to $\mathbb Z^8$ or to $E$** (O'Meara 1973, §106F,
p. 334, "if $J \cong I_8$ then $K \cong I_8$ if $K$ splits and $K \cong \Phi_8$ if $K$ does not split"). For
$y \in K - D$ the vector $2y$ has integer coordinates $a_i$, $\sum a_i^2 \equiv 0 \bmod 4$, so exactly $4$ or $8$ of the
$a_i$ are odd. With $4$ odd coordinates `key_norm_one` applies to $w = \tfrac12\sum_{a_i\ \mathrm{odd}}x_i$ and gives
$K \cong D$ (106:9 or splitting + 106:10); with $8$, `isIsometric_E_of_all_odd` gives $K \cong E$. -/
theorem omeara_adj_D_rank8 {K : Submodule (𝓞 ℚ) (Fin 8 → ℚ)} (hlat : K.IsLattice ℚ)
    (hK : IsUnimodularZ (sumSqForm 8) K) (hadj : Nbr.IsNbrL (sumSqForm 8) 2 K intVec) :
    IsIsometric (sumSqForm 8) intVec K ∨ IsIsometric (sumSqForm 8) (omearaE 8) K := by
  classical
  have hD : IsUnimodularZ (sumSqForm 8) (intVec : Submodule (𝓞 ℚ) (Fin 8 → ℚ)) := adj_D_unimodular
  obtain ⟨y, hyK, hyD⟩ := r9_exists_out hadj
  have h2y : (2 : ℚ) • y ∈ (intVec : Submodule (𝓞 ℚ) (Fin 8 → ℚ)) := r9_two_smul_mem hadj hyK
  have ha0 : ∀ i, ∃ a : ℤ, 2 * y i = a := fun i => by
    obtain ⟨m, hm⟩ := r9_D_coord.mp h2y i
    exact ⟨m, by simpa using hm⟩
  choose a ha using ha0
  have hy : ∀ i, y i = (a i : ℚ) / 2 := fun i => by linarith [ha i]
  obtain ⟨m, hm⟩ := uni_Q_int _ hK hyK
  rw [r9_eval] at hm
  have h4 : 4 ∣ ∑ i, a i ^ 2 := by
    refine ⟨m, ?_⟩
    have : ((∑ i, a i ^ 2 : ℤ) : ℚ) = 4 * m := by
      push_cast
      rw [← hm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hy i]; ring
    exact_mod_cast this
  set S : Finset (Fin 8) := Finset.univ.filter fun i => a i % 2 = 1 with hSdef
  have hmem : ∀ i, i ∈ S ↔ a i % 2 = 1 := fun i => by simp [hSdef]
  have hmod : (∑ i, a i ^ 2) % 4 = (S.card : ℤ) % 4 := by
    rw [Finset.sum_int_mod]
    have : ∀ i ∈ (Finset.univ : Finset (Fin 8)), a i ^ 2 % 4 = if a i % 2 = 1 then 1 else 0 :=
      fun i _ => r9_sq_mod4 (a i)
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    simp only [mul_one]
    rfl
  have hne : S.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    apply hyD
    refine r9_D_coord.mpr fun i => ?_
    have hi : ¬ a i % 2 = 1 := fun h => by
      have := (hmem i).mpr h; rw [hcon] at this; simp at this
    obtain ⟨r, hr⟩ : ∃ r, a i = 2 * r := ⟨a i / 2, by omega⟩
    exact ⟨r, by rw [hy i, hr]; push_cast; ring⟩
  have hpos : 0 < S.card := Finset.card_pos.mpr hne
  have hle : S.card ≤ 8 := by simpa using Finset.card_le_univ S
  have h0 : (S.card : ℤ) % 4 = 0 := by rw [← hmod]; omega
  have hc48 : S.card = 4 ∨ S.card = 8 := by omega
  rcases hc48 with hc | hc
  · left
    set w : Fin 8 → ℚ := fun i => if i ∈ S then 1 / 2 else 0 with hw
    have hw1 : (sumSqForm 8).eval w = 1 := by
      rw [r9_eval]
      have : ∀ i, w i ^ 2 = if i ∈ S then (1 / 4 : ℚ) else 0 := fun i => by
        by_cases h : i ∈ S <;> simp [hw, h]; norm_num
      rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_filter]
      have e : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
      rw [e, Finset.sum_const, hc]
      norm_num
    have hyw : y - w ∈ (intVec : Submodule (𝓞 ℚ) (Fin 8 → ℚ)) := by
      refine r9_D_coord.mpr fun i => ?_
      by_cases hi : i ∈ S
      · have h1 := (hmem i).mp hi
        obtain ⟨r, hr⟩ : ∃ r, a i = 2 * r + 1 := ⟨a i / 2, by omega⟩
        exact ⟨r, by simp [hw, hi, hy i, hr]; ring⟩
      · have h1 : ¬ a i % 2 = 1 := fun h => hi ((hmem i).mpr h)
        obtain ⟨r, hr⟩ : ∃ r, a i = 2 * r := ⟨a i / 2, by omega⟩
        exact ⟨r, by simp [hw, hi, hy i, hr]⟩
    rcases key_norm_one (sumSqForm 8) hD hK hadj hyK hyD hw1 hyw with hwK | hiso
    · exact isIsometric_of_norm_one_rank8 hlat hK hwK hw1
    · exact hiso.symm
  · right
    have hS : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hc)
    refine isIsometric_E_of_all_odd hK hadj hyK fun i => ⟨a i, ha i, ?_⟩
    exact (hmem i).mp (by rw [hS]; exact Finset.mem_univ i)

/-- **The unimodular lattices on $I_8$** (O'Meara 1973, §106F, 106:13 for $n = 8$, p. 334): every unimodular lattice
$L$ on $V = I_8$ is isometric to $D = \mathbb Z^8$ or to $E$ (`omearaE 8`).

Proof as in the book: by 106:2 move $L$ into $\mathcal G(D)$ (within its proper class), join it to $D$ by a chain of
adjacent unimodular lattices (106:4), and show by induction along the chain that every member is isometric to $D$ or
$E$: a lattice adjacent to (a copy of) $D$ is isometric to $D$ or $E$ (`omeara_adj_D_rank8`), a lattice adjacent to
(a copy of) $E$ is isometric to $D$ or $E$ (106:12, `omeara106_12`); the isometries are transported to the base
lattice with `r9_transport`. -/
@[kb "omeara1963" "§106F, 106:13, p. 334 (the case n = 8)"]
theorem unimodular_rank8(L : Lat ℚ 8) (hL : IsUnimodularZ (sumSqForm 8) L.1) :
    IsIsometric (sumSqForm 8) intVec L.1 ∨ IsIsometric (sumSqForm 8) (omearaE 8) L.1 := by
  let D : Lat ℚ 8 := ⟨intVec, intVec_isLattice⟩
  have hD : IsUnimodularZ (sumSqForm 8) D.1 := adj_D_unimodular
  obtain ⟨J, hJp, hJG⟩ := omeara106_2.holds 8 (by norm_num) L D hL hD
  have hJ : IsIsometric (sumSqForm 8) intVec J.1 ∨ IsIsometric (sumSqForm 8) (omearaE 8) J.1 := by
    by_cases hJD : J = D
    · exact Or.inl (hJD ▸ IsIsometric.refl _ _)
    · have hchain := omeara106_4 (sumSqForm 8) (L := D) hD hJG hJD
      have hall : ∀ Z : Submodule (𝓞 ℚ) (Fin 8 → ℚ),
          Relation.TransGen (fun A B => IsUnimodularZ (sumSqForm 8) A ∧ IsUnimodularZ (sumSqForm 8) B ∧
            Nbr.IsNbrL (sumSqForm 8) 2 A B) D.1 Z →
          Z.IsLattice ℚ ∧ (IsIsometric (sumSqForm 8) intVec Z ∨ IsIsometric (sumSqForm 8) (omearaE 8) Z) := by
        intro Z hZ
        induction hZ with
        | single hR =>
          obtain ⟨-, hZu, hadj⟩ := hR
          have hlat := r9_isLattice_nbr intVec_isLattice hadj
          exact ⟨hlat, omeara_adj_D_rank8 hlat hZu hadj.symm⟩
        | tail _ hR ih =>
          rename_i b c
          obtain ⟨-, hcu, hadj⟩ := hR
          obtain ⟨hblat, hb⟩ := ih
          have hclat := r9_isLattice_nbr hblat hadj
          refine ⟨hclat, ?_⟩
          rcases hb with hb | hb
          · obtain ⟨Y0, hY0u, hY0adj, hY0c⟩ := r9_transport hb hcu hadj
            have hY0lat := r9_isLattice_nbr intVec_isLattice hY0adj
            rcases omeara_adj_D_rank8 hY0lat hY0u hY0adj.symm with h | h
            · exact Or.inl (IsIsometric.trans _ h hY0c)
            · exact Or.inr (IsIsometric.trans _ h hY0c)
          · obtain ⟨Y0, hY0u, hY0adj, hY0c⟩ := r9_transport hb hcu hadj
            rcases omeara106_12 hY0u hY0adj.symm with h | h
            · exact Or.inl (IsIsometric.trans _ h hY0c)
            · exact Or.inr (IsIsometric.trans _ h hY0c)
      exact (hall _ hchain).2
  have hJL : IsIsometric (sumSqForm 8) J.1 L.1 := hJp.symm.isIsometric
  rcases hJ with h | h
  · exact Or.inl (IsIsometric.trans _ h hJL)
  · exact Or.inr (IsIsometric.trans _ h hJL)

end Rank8

/-! ### 106:13 for $n = 9$ -/

section Rank9

/-- The splitting $L' \perp \mathbb Z$ respects isometries of $L'$. -/
lemma isIsometric_splitLat {k : ℕ} {M L' : Submodule (𝓞 ℚ) (Fin k → ℚ)}
    (h : IsIsometric (sumSqForm k) M L') : IsIsometric (sumSqForm (k + 1)) (splitLat M) (splitLat L') := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact ⟨blkGL γ, blkGL_mem_orth hγ, glImage_blkGL_splitLat γ M⟩

/-- $E_8 \perp \mathbb Z^{1}$ is $E_8 \perp \mathbb Z$: `omearaEZ 9 = splitLat (omearaE 8)`. -/
lemma omearaEZ_nine : omearaEZ 9 = splitLat (omearaE 8) := by
  ext x
  rw [mem_omearaEZ, mem_splitLat]
  have hh : omearaEZHead 9 x = fun i : Fin 8 => x (Fin.castSucc i) := by
    funext j
    simp only [omearaEZHead, LinearMap.coe_mk, AddHom.coe_mk]
    have hj : (j : ℕ) < 9 := by omega
    simp only [hj, dite_true]
    rfl
  rw [hh]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h
    exact h (Fin.last 8) (by simp)
  · intro h i hi
    have : i = Fin.last 8 := Fin.ext (by have := i.isLt; simp; omega)
    rw [this]
    exact h

private lemma r9_bil_zero_left {n : ℕ} (x : Fin n → ℚ) : bil (sumSqForm n) 0 x = 0 := by
  simp [bil]

/-- A norm-$1$ vector is carried to a norm-$1$ vector by an isometry of lattices. -/
private lemma r9_rep1_of_isIsometric {n : ℕ} {Y0 Z : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (h : IsIsometric (sumSqForm n) Y0 Z) (hw : ∃ w ∈ Y0, (sumSqForm n).eval w = 1) :
    ∃ w ∈ Z, (sumSqForm n).eval w = 1 := by
  obtain ⟨γ, hγ, rfl⟩ := h
  obtain ⟨w, hw, hw1⟩ := hw
  refine ⟨γ.val *ᵥ w, mulVec_mem_glImage hw, ?_⟩
  have := evalIn_mulVec_of_mem (sumSqForm n) hγ w
  change (sumSqForm n).evalIn ℚ _ = _ at this
  change (sumSqForm n).evalIn ℚ _ = 1
  rw [this]
  exact hw1

/-- **A unimodular lattice adjacent to $\mathbb Z^n$ represents $1$ when $4 \nmid n$** (O'Meara 1973, §106F, p. 335,
the case $J' \cong I_8$ of the key step for $n = 9$: "at least one $m_i$ is even since $Q(y) \in \mathbb Z$"). Let $K$ be
unimodular and adjacent to $D = \mathbb Z^n$. For $y \in K - D$ the integers $a_i = 2y_i$ satisfy
$\sum a_i^2 \equiv 0 \bmod 4$, so not all are odd; for $a_i$ even $x_i \in D \cap K$ (106:6) has norm $1$. -/
theorem rep1_adj_D {n : ℕ} (hn : ¬ 4 ∣ n) {K : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hK : IsUnimodularZ (sumSqForm n) K) (hadj : Nbr.IsNbrL (sumSqForm n) 2 K intVec) :
    ∃ w ∈ K, (sumSqForm n).eval w = 1 := by
  classical
  have hD : IsUnimodularZ (sumSqForm n) (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := adj_D_unimodular
  obtain ⟨y, hyK, hyD⟩ := r9_exists_out hadj
  have h2y : (2 : ℚ) • y ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := r9_two_smul_mem hadj hyK
  have ha0 : ∀ i, ∃ a : ℤ, 2 * y i = a := fun i => by
    obtain ⟨m, hm⟩ := r9_D_coord.mp h2y i
    exact ⟨m, by simpa using hm⟩
  choose a ha using ha0
  have hy : ∀ i, y i = (a i : ℚ) / 2 := fun i => by linarith [ha i]
  obtain ⟨m, hm⟩ := uni_Q_int _ hK hyK
  rw [r9_eval] at hm
  have h4 : 4 ∣ ∑ i, a i ^ 2 := by
    refine ⟨m, ?_⟩
    have : ((∑ i, a i ^ 2 : ℤ) : ℚ) = 4 * m := by
      push_cast
      rw [← hm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hy i]; ring
    exact_mod_cast this
  obtain ⟨i0, hi0⟩ : ∃ i0, a i0 % 2 = 0 := by
    by_contra hcon
    push Not at hcon
    have hodd : ∀ i, a i % 2 = 1 := fun i => by have := hcon i; omega
    have hmod : (∑ i, a i ^ 2) % 4 = (n : ℤ) % 4 := by
      rw [Finset.sum_int_mod]
      have : ∀ i ∈ (Finset.univ : Finset (Fin n)), a i ^ 2 % 4 = 1 := fun i _ => by
        rw [r9_sq_mod4]; simp [hodd i]
      rw [Finset.sum_congr rfl this]
      simp
    apply hn
    have h0 : (n : ℤ) % 4 = 0 := by rw [← hmod]; omega
    omega
  obtain ⟨r, hr⟩ : ∃ r, a i0 = 2 * r := ⟨a i0 / 2, by omega⟩
  have hyi : y i0 = r := by rw [hy i0, hr]; push_cast; ring
  set e : Fin n → ℚ := Pi.single i0 1 with he
  have heD : e ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := r9_D_coord.mpr fun j => by
    by_cases h : j = i0
    · subst h; exact ⟨1, by simp [he]⟩
    · exact ⟨0, by simp [he, h]⟩
  have hbil : bil (sumSqForm n) e y / 2 = r := by
    rw [r9_bil, he]
    simp [Pi.single_apply, hyi]
  have heK : e ∈ K ⊓ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) :=
    ((omeara106_6 (sumSqForm n) hD hK hadj hyK hyD).2.2.2 e).mpr ⟨heD, r, hbil⟩
  refine ⟨e, (Submodule.mem_inf.mp heK).1, ?_⟩
  rw [r9_eval, he]
  simp [Pi.single_apply]

/-- **A unimodular lattice adjacent to $E_8 \perp \mathbb Z$ represents $1$** (O'Meara 1973, §106F, p. 335, the case
$J' \cong \Phi_8$ of the key step for $n = 9$: "$J'$ is even, so $Q(y) \in \mathbb Z$ forces $m \in 2\mathbb Z$"). If $K$
is unimodular and adjacent to $J = E_8 \perp \mathbb Z$ (`omearaEZ 9`) then for $y \in K - J$ the last coordinate
$2y_8 = a$ is an integer with $a^2 = 4Q(y) - Q(2y_{\mathrm{init}}) \in 2\mathbb Z$ ($E_8$ is even), so $a$ is even and
$x_8 \in J \cap K$ (106:6) has norm $1$. -/
theorem rep1_adj_EZ_nine {K : Submodule (𝓞 ℚ) (Fin 9 → ℚ)} (hK : IsUnimodularZ (sumSqForm 9) K)
    (hadj : Nbr.IsNbrL (sumSqForm 9) 2 K (omearaEZ 9)) : ∃ w ∈ K, (sumSqForm 9).eval w = 1 := by
  rw [omearaEZ_nine] at hadj
  obtain ⟨hE8, -, -⟩ := omeara106_r29_adjacent (n := 8) (by norm_num) le_rfl
  have hZ : IsUnimodularZ (sumSqForm 9) (splitLat (omearaE 8)) := splitLat_unimodular hE8
  obtain ⟨y, hyK, hyZ⟩ := r9_exists_out hadj
  have h2y : (2 : ℚ) • y ∈ splitLat (omearaE 8) := r9_two_smul_mem hadj hyK
  obtain ⟨hinit, a, ha⟩ := h2y
  have hu : (fun i : Fin 8 => (2 : ℚ) * y (Fin.castSucc i)) ∈ omearaE 8 := by simpa using hinit
  obtain ⟨q, hq⟩ := omearaE_even (by norm_num) le_rfl _ hu
  obtain ⟨m', hm'⟩ := uni_Q_int _ hK hyK
  rw [r9_eval, r9_sum_succ] at hm'
  rw [r9_eval] at hq
  have hq' : ∑ i : Fin 8, (2 * y (Fin.castSucc i)) ^ 2 = 2 * (q : ℚ) := by simpa using hq
  have ha' : 2 * y (Fin.last 8) = a := by simpa using ha
  have hsumY : ∑ i : Fin 8, (2 * y (Fin.castSucc i)) ^ 2 = 4 * ∑ i : Fin 8, y (Fin.castSucc i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : ((a ^ 2 : ℤ) : ℚ) = ((4 * m' - 2 * q : ℤ) : ℚ) := by
    push_cast
    have : (a : ℚ) ^ 2 = 4 * y (Fin.last 8) ^ 2 := by rw [← ha']; ring
    rw [this]
    linarith
  have hsqZ : a ^ 2 = 4 * m' - 2 * q := by exact_mod_cast hsq
  have heven : a % 2 = 0 := by
    have h := r9_sq_mod4 a
    generalize a ^ 2 = s at h hsqZ
    split_ifs at h <;> omega
  obtain ⟨b, hb⟩ : ∃ b, a = 2 * b := ⟨a / 2, by omega⟩
  have hyl : y (Fin.last 8) = b := by
    have : (a : ℚ) = 2 * b := by rw [hb]; push_cast; ring
    linarith
  set e : Fin 9 → ℚ := spExt (0 : Fin 8 → ℚ) 1 with he
  have heZ : e ∈ splitLat (omearaE 8) := ⟨r9_spExt_zero_mem _, 1, by rw [he, spExt_last]; simp⟩
  have hbil : bil (sumSqForm 9) e y / 2 = b := by
    have := bil_eta_left (0 : Fin 8 → ℚ) 1 y
    rw [r9_bil_zero_left] at this
    change bil (sumSqForm 9) e y = _ at this
    rw [this, hyl]
    ring
  have heK : e ∈ K ⊓ splitLat (omearaE 8) :=
    ((omeara106_6 (sumSqForm 9) hZ hK hadj hyK hyZ).2.2.2 e).mpr ⟨heZ, b, hbil⟩
  exact ⟨e, (Submodule.mem_inf.mp heK).1, r9_eval_spExt_zero_one 8⟩

/-- **A unimodular lattice on $I_9$ representing $1$** is isometric to $\mathbb Z^9$ or to $E_8 \perp \mathbb Z^1$
(`omearaEZ 9`): split off the vector of norm $1$ (`unimodular_split_unit`) and apply the classification of the
unimodular lattices on $I_8$ (`unimodular_rank8`) to the complement. -/
theorem unimodular_rank9_of_rep1 {L : Lat ℚ 9} (hL : IsUnimodularZ (sumSqForm 9) L.1)
    (h1 : ∃ w ∈ L.1, (sumSqForm 9).eval w = 1) :
    IsIsometric (sumSqForm 9) intVec L.1 ∨ IsIsometric (sumSqForm 9) (omearaEZ 9) L.1 := by
  obtain ⟨w, hw, hw1⟩ := h1
  obtain ⟨σ, L', hσ, hL', hσL⟩ := unimodular_split_unit (k := 8) hL hw hw1
  have hback : IsIsometric (sumSqForm 9) (glImage σ L.1) L.1 :=
    ⟨σ⁻¹, (orthGroup _ ℚ).inv_mem hσ, by rw [← glImage_mul, inv_mul_cancel, glImage_one]⟩
  rcases unimodular_rank8 L' hL' with h | h
  · left
    have h2 := isIsometric_splitLat h
    rw [splitLat_intVec, ← hσL] at h2
    exact IsIsometric.trans _ h2 hback
  · right
    have h2 := isIsometric_splitLat h
    rw [← omearaEZ_nine, ← hσL] at h2
    exact IsIsometric.trans _ h2 hback

/-- **A unimodular lattice on $I_9$ (in the chain from $D$) represents $1$**: if $J$ and $K$ are adjacent unimodular
lattices, $J$ a lattice representing $1$, then $K$ represents $1$ (O'Meara 1973, §106F, pp. 334–335). The proof splits
$J$ (`unimodular_rank9_of_rep1`: $J \cong \mathbb Z^9$ or $E_8 \perp \mathbb Z$), transports $K$ to a neighbour of
$\mathbb Z^9$ or of $E_8 \perp \mathbb Z$ (`r9_transport`) and applies `rep1_adj_D` or `rep1_adj_EZ_nine`. -/
theorem rep1_of_adjacent_rank9 {J K : Submodule (𝓞 ℚ) (Fin 9 → ℚ)} (hJlat : J.IsLattice ℚ)
    (hJ : IsUnimodularZ (sumSqForm 9) J) (hK : IsUnimodularZ (sumSqForm 9) K)
    (hadj : Nbr.IsNbrL (sumSqForm 9) 2 J K) (hrep : ∃ w ∈ J, (sumSqForm 9).eval w = 1) :
    ∃ w ∈ K, (sumSqForm 9).eval w = 1 := by
  have hcls := unimodular_rank9_of_rep1 (L := ⟨J, hJlat⟩) hJ hrep
  rcases hcls with h | h
  · obtain ⟨Y0, hY0u, hY0adj, hY0c⟩ := r9_transport h hK hadj
    exact r9_rep1_of_isIsometric hY0c (rep1_adj_D (by norm_num) hY0u hY0adj.symm)
  · obtain ⟨Y0, hY0u, hY0adj, hY0c⟩ := r9_transport h hK hadj
    exact r9_rep1_of_isIsometric hY0c (rep1_adj_EZ_nine hY0u hY0adj.symm)

/-- **The unimodular lattices on $I_9$** (O'Meara 1973, §106F, 106:13 for $n = 9$, pp. 334–335): every unimodular lattice
$L$ on $V = I_9$ is isometric to $\mathbb Z^9$ or to $E_8 \perp \mathbb Z$ (`omearaEZ 9`). By 106:2 and 106:4 reduce to a
chain of adjacent unimodular lattices from $D$; every member represents $1$ (`rep1_of_adjacent_rank9`), hence splits
and is isometric to $\mathbb Z^9$ or $E_8 \perp \mathbb Z$ (`unimodular_rank9_of_rep1`, using `unimodular_rank8`). -/
@[kb "omeara1963" "§106F, 106:13, pp. 334–335 (the case n = 9)"]
theorem unimodular_rank9(L : Lat ℚ 9) (hL : IsUnimodularZ (sumSqForm 9) L.1) :
    IsIsometric (sumSqForm 9) intVec L.1 ∨ IsIsometric (sumSqForm 9) (omearaEZ 9) L.1 := by
  let D : Lat ℚ 9 := ⟨intVec, intVec_isLattice⟩
  have hD : IsUnimodularZ (sumSqForm 9) D.1 := adj_D_unimodular
  obtain ⟨J, hJp, hJG⟩ := omeara106_2.holds 9 (by norm_num) L D hL hD
  have hJ : IsIsometric (sumSqForm 9) intVec J.1 ∨ IsIsometric (sumSqForm 9) (omearaEZ 9) J.1 := by
    by_cases hJD : J = D
    · exact Or.inl (hJD ▸ IsIsometric.refl _ _)
    · have hchain := omeara106_4 (sumSqForm 9) (L := D) hD hJG hJD
      have hall : ∀ Z : Submodule (𝓞 ℚ) (Fin 9 → ℚ),
          Relation.TransGen (fun A B => IsUnimodularZ (sumSqForm 9) A ∧ IsUnimodularZ (sumSqForm 9) B ∧
            Nbr.IsNbrL (sumSqForm 9) 2 A B) D.1 Z →
          Z.IsLattice ℚ ∧ ∃ w ∈ Z, (sumSqForm 9).eval w = 1 := by
        intro Z hZ
        induction hZ with
        | single hR =>
          obtain ⟨-, hZu, hadj⟩ := hR
          exact ⟨r9_isLattice_nbr intVec_isLattice hadj, rep1_adj_D (by norm_num) hZu hadj.symm⟩
        | tail _ hR ih =>
          rename_i b c
          obtain ⟨hbu, hcu, hadj⟩ := hR
          obtain ⟨hblat, hbrep⟩ := ih
          exact ⟨r9_isLattice_nbr hblat hadj, rep1_of_adjacent_rank9 hblat hbu hcu hadj hbrep⟩
      obtain ⟨hlat, hrep⟩ := hall _ hchain
      exact unimodular_rank9_of_rep1 (L := J) hJG.1 hrep
  have hJL : IsIsometric (sumSqForm 9) J.1 L.1 := hJp.symm.isIsometric
  rcases hJ with h | h
  · exact Or.inl (IsIsometric.trans _ h hJL)
  · exact Or.inr (IsIsometric.trans _ h hJL)

/-- **Theorem 106:13** (O'Meara 1973, §106F, p. 334). Let $V$ be the $n$-ary positive definite space $I_n$ over $\mathbb Q$
with $1 \le n \le 9$ and $L$ a unimodular lattice on $V$ (`hL : IsUnimodularZ (sumSqForm n) L.1`, $L^\# = L$). Then $L$
has exactly one of the forms $I_n$, $\Phi_8 \perp I_{n-8}$ ($n \ge 8$): precisely one of
`IsIsometric (sumSqForm n) intVec L.1` ($L \cong \mathbb Z^n$, matrix $I_n$) and
`8 ≤ n ∧ IsIsometric (sumSqForm n) (omearaEZ n) L.1` ($L \cong E_8 \perp \mathbb Z^{n-8}$, matrix $\Phi_8 \perp I_{n-8}$)
holds (`Xor`). For $n = 8$, $\Phi_8$ is $E$ (`omearaEZ_eq_omearaE_eight`).

*Proof.* "At most one": `not_isIsometric_intVec_omearaEZ` (O'Meara: 105:1 and indecomposability of $\Phi_8$, replaced by a
more elementary argument, see `Sec106EZ.lean`). "At least one": for $n \le 7$ by 106:10 (`omeara106_10_uncond`), for
$n = 8$ by `unimodular_rank8` (106:2, 106:4, 106:12 and the adjacent-lattice analysis), for $n = 9$ by `unimodular_rank9`
(every lattice of the chain represents $1$, then it splits). Unconditional: 106:2 is proved in `Sec106Two.lean`. -/
@[kb "omeara1963" "§106F, 106:13, p. 334"]
theorem omeara106_13 {n : ℕ} (h1 : 1 ≤ n) (h9 : n ≤ 9) {L : Lat ℚ n}
    (hL : IsUnimodularZ (sumSqForm n) L.1) :
    Xor (IsIsometric (sumSqForm n) intVec L.1) (8 ≤ n ∧ IsIsometric (sumSqForm n) (omearaEZ n) L.1) := by
  have hex : IsIsometric (sumSqForm n) intVec L.1 ∨ (8 ≤ n ∧ IsIsometric (sumSqForm n) (omearaEZ n) L.1) := by
    rcases (by omega : n ≤ 7 ∨ n = 8 ∨ n = 9) with h | rfl | rfl
    · exact Or.inl (omeara106_10_uncond h1 h hL)
    · rcases unimodular_rank8 L hL with h | h
      · exact Or.inl h
      · exact Or.inr ⟨le_rfl, by rw [omearaEZ_eq_omearaE_eight]; exact h⟩
    · rcases unimodular_rank9 L hL with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by norm_num, h⟩
  have hnot : 8 ≤ n → ¬ (IsIsometric (sumSqForm n) intVec L.1 ∧ IsIsometric (sumSqForm n) (omearaEZ n) L.1) :=
    fun hn ⟨ha, hb⟩ => not_isIsometric_intVec_omearaEZ hn (IsIsometric.trans _ ha hb.symm)
  rcases hex with ha | hb
  · exact Or.inl ⟨ha, fun hb => hnot hb.1 ⟨ha, hb.2⟩⟩
  · exact Or.inr ⟨hb, fun ha => hnot hb.1 ⟨ha, hb.2⟩⟩

end Rank9

/-! ### 106.r38: the classification up to $n = 13$ (Kneser), stated -/

section Rank13

/-- **The head map** $\mathbb Q^n \to \mathbb Q^m$: the first $m$ coordinates, zero-padded if $n < m$. $\mathcal O_{\mathbb
Q}$-linear. Auxiliary; `omearaEPerpHead 8 n` is `omearaEZHead n`. -/
def omearaEPerpHead (m n : ℕ) : (Fin n → ℚ) →ₗ[𝓞 ℚ] (Fin m → ℚ) where
  toFun x j := if h : j.val < n then x ⟨j.val, h⟩ else 0
  map_add' x y := by
    ext j
    by_cases h : j.val < n <;> simp [h]
  map_smul' c x := by
    ext j
    by_cases h : j.val < n <;> simp [h]

/-- **The tail condition**: the vectors all of whose coordinates $x_i$ with $i \ge m$ are integers. Auxiliary. -/
def omearaEPerpTail (m n : ℕ) : Submodule (𝓞 ℚ) (Fin n → ℚ) where
  carrier := {x | ∀ i : Fin n, m ≤ i.val → ∃ k : ℤ, x i = k}
  add_mem' {x y} hx hy i hi := by
    obtain ⟨a, ha⟩ := hx i hi
    obtain ⟨b, hb⟩ := hy i hi
    exact ⟨a + b, by simp [ha, hb]⟩
  zero_mem' i hi := ⟨0, by simp⟩
  smul_mem' c x hx i hi := by
    obtain ⟨j, hj⟩ := exists_int_smul_eq c x
    obtain ⟨a, ha⟩ := hx i hi
    exact ⟨j * a, by rw [hj]; simp [ha]⟩

/-- **The lattice $E_m \perp \mathbb Z^{n-m}$** inside $\mathbb Q^n$ with $Q = I_n$ (meaningful for $4 \mid m$,
$m \ge 8$, $n \ge m$): the vectors whose first $m$ coordinates lie in $E_m$ (`omearaE m`) and whose other coordinates
are integers. For $m = 8$ it is `omearaEZ n` (`omearaEPerp_eight`), for $n = m$ it is `omearaE m`
(`omearaEPerp_self`). O'Meara's matrix $\Phi_m \perp I_{n-m}$ (used in the remark after 106:13 for $m = 12$). -/
@[kb "omeara1963" "§106F, p. 335 (the lattice with matrix Φ₁₂ ⊥ I_{n−12}, and Φ₈ ⊥ I_{n−8})"]
def omearaEPerp (m n : ℕ) : Submodule (𝓞 ℚ) (Fin n → ℚ) :=
  (omearaE m).comap (omearaEPerpHead m n) ⊓ omearaEPerpTail m n

/-- $E_8 \perp \mathbb Z^{n-8}$ via the general definition is `omearaEZ n`. -/
lemma omearaEPerp_eight (n : ℕ) : omearaEPerp 8 n = omearaEZ n := rfl

/-- $E_m \perp \mathbb Z^0 = E_m$. -/
lemma omearaEPerp_self (m : ℕ) : omearaEPerp m m = omearaE m := by
  ext x
  have hh : omearaEPerpHead m m x = x := by
    funext j
    simp [omearaEPerpHead]
  constructor
  · rintro ⟨h, -⟩
    simpa [hh] using h
  · intro h
    exact ⟨by simpa [hh] using h, fun i hi => absurd i.isLt (by omega)⟩

/-- **106.r38 — named statement** (O'Meara 1973, §106F, p. 335, the remark after 106:13; due to Kneser, *Arch. Math.*
1957, pp. 241–250; **not proved in the book**, and not proved here): for $1 \le n \le 13$ the proper classes of unimodular
lattices on $V = I_n$ over $\mathbb Q$ are those of $I_n$ (`intVec`), $\Phi_8 \perp I_{n-8}$ ($n \ge 8$, `omearaEZ n`) and
$\Phi_{12} \perp I_{n-12}$ ($n \ge 12$, `omearaEPerp 12 n`, which is `omearaE 12` for $n = 12$).

The structure has three fields. `unimodular`: the listed lattices are unimodular. `covers`: every unimodular lattice
$L$ on $I_n$ is properly isometric to one of the listed lattices. `distinct`: the listed lattices are pairwise
non-isometric. (The book states only that the proper classes "are determined by" these lattices; `unimodular` and
`distinct` are the evident reading of "determined".) This is a *stated* remark that is never assumed in a theorem of
the repository. For $n \le 9$ it is the theorem `omeara106_13`. -/
@[kb "omeara1963" "§106F, 106.r38, p. 335 (Kneser 1957: proper classes for 1 ≤ n ≤ 13; stated, not proved in the book)"]
structure OMeara106_r38 : Prop where
  /-- The listed lattices are unimodular. -/
  unimodular : ∀ n : ℕ, (8 ≤ n → IsUnimodularZ (sumSqForm n) (omearaEZ n)) ∧
    (12 ≤ n → IsUnimodularZ (sumSqForm n) (omearaEPerp 12 n))
  /-- Every unimodular lattice on $I_n$, $1 \le n \le 13$, is properly isometric to one of the listed lattices. -/
  covers : ∀ n : ℕ, 1 ≤ n → n ≤ 13 → ∀ L : Lat ℚ n, IsUnimodularZ (sumSqForm n) L.1 →
    IsProperIsometric (sumSqForm n) intVec L.1 ∨
      (8 ≤ n ∧ IsProperIsometric (sumSqForm n) (omearaEZ n) L.1) ∨
      (12 ≤ n ∧ IsProperIsometric (sumSqForm n) (omearaEPerp 12 n) L.1)
  /-- The listed lattices are pairwise non-isometric. -/
  distinct : ∀ n : ℕ, n ≤ 13 →
    (8 ≤ n → ¬ IsIsometric (sumSqForm n) intVec (omearaEZ n)) ∧
    (12 ≤ n → ¬ IsIsometric (sumSqForm n) intVec (omearaEPerp 12 n)) ∧
    (12 ≤ n → ¬ IsIsometric (sumSqForm n) (omearaEZ n) (omearaEPerp 12 n))

end Rank13

end QuadFormsKB.Lattices
