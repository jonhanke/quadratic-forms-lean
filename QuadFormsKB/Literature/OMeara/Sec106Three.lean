/-
# O'Meara §106B: Proposition 106:3, proved

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^n$ with $Q = x_0^2 + \dots + x_{n-1}^2$ (`sumSqForm n`, O'Meara's $V = I_n$),
lattices `Lat ℚ n`, O'Meara's $B = \tfrac12$ `bil Q`, unimodular lattices `IsUnimodularZ` ($L^\# = L$), even lattices
`IsEvenLat` ($Q(L) \subseteq 2\mathbb Z$), adjacency = `Nbr.IsNbrL Q 2` (Kneser's $2$-neighbours; for unimodular lattices
O'Meara's invariant factors $\tfrac12\mathbb Z, \mathbb Z, \dots, \mathbb Z, 2\mathbb Z$, see `Sec106C.lean`),
$D = \mathbb Z^n$ = `intVec`, $E$ = `omearaE n`. Localizations $L_p$ = `loc v L` at the finite spots `v`; the local
isometries are matrices of `orthGroup` acting by `locAct`. Indices are 0-based.

**Proves**
* **`omeara106_3_holds`** (**Proposition 106:3**, O'Meara 1973, §106B, p. 326): the named statement `OMeara106_3`
  (`Sec106Class.lean`) holds: for $8 \mid n$, $n > 0$, every unimodular lattice $L$ on $I_n$ has an even and an odd
  unimodular lattice adjacent to it. **Unconditional.**
* `exists_adjacent_of_sameParity` (the transfer step): if $N$ is adjacent to $M$, all three of $L, M, N$ are unimodular
  and $L, M$ have the same parity, then some unimodular $K$ adjacent to $L$ has the parity of $N$.
* `loc_inf` ($(A \cap B)_\mathfrak p = A_\mathfrak p \cap B_\mathfrak p$ for lattices over a number field) and
  `locAct_inf` (auxiliary).

**Deviation from the book's proof** (*Update:* a simplification).
O'Meara uses the dyadic classification (Example 93:18: $L_2$ is
$A(0,0)^{n/2}$ or $A(0,0)^{n/2-1} \perp A(1,0)$) to write down a local lattice $K_2$ of the wanted parity adjacent to
$L_2$, and glues $K_2$ with the $L_p$, $p$ odd (81:14). Here the explicit dyadic shapes are avoided. Two unimodular
lattices of the same parity have the same scale $\mathbb Z$ and the same norm ($\mathbb Z$ or $2\mathbb Z$), hence lie
in one genus (93:29 at $2$, 92:2 at odd $p$: `sameGenus_of_isModularLat_rat`). So one compares $L$ with a model $M$ of
its parity that has an adjacent unimodular $N$ of the wanted parity ($D \sim E$, an odd neighbour of $D$ through
$y = \tfrac12(x_0 + x_1 + x_2 + x_3)$, an even neighbour of $E$ through $y = \tfrac12(x_0 + \dots + x_{n-2} - x_{n-1})$,
all from 106:7), takes $g_p \in O(V_p)$ with $g_pM_p = L_p$ at every $p$, and glues $K_p = g_pN_p$ (81:14,
`LocFamily.glue`). Then $K$ is in the genus of $N$ (so $\mathfrak sK = \mathbb Z$, $\mathfrak vK = \mathbb Z$, and $K$
is unimodular), has the parity of $N$ (parity is seen at $2$, 106.r15), and $K \cap L$ is in the genus of $N \cap M$,
so $\mathfrak v(K \cap L) = \mathfrak v(N \cap M) = 4\mathbb Z$ and $K$ is adjacent to $L$ (106:5).
-/
import QuadFormsKB.Literature.OMeara.Sec106Class
import QuadFormsKB.Literature.OMeara.Sec106EZ
import QuadFormsKB.Literature.OMeara.Sec106Facts
import QuadFormsKB.Literature.OMeara.Sec104Ten
import QuadFormsKB.Literature.OMeara.Sec102Volume
import QuadFormsKB.Literature.OMeara.Sec102Three

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

section General

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Completion commutes with intersections of lattices** (O'Meara 1963, §81E, p. 218): for lattices $A, B$ on $F^n$
(hypotheses `hA`, `hB`) and a finite spot $\mathfrak p$ (`v`), $(A \cap B)_\mathfrak p = A_\mathfrak p \cap B_\mathfrak p$.
*Proof:* the family $(A_\mathfrak q \cap B_\mathfrak q)_\mathfrak q$ is a family of local lattices, almost all standard;
its gluing is $A \cap B$ (a lattice is the set of vectors in all its completions), and the gluing has the given
completions (81:14, `LocFamily.loc_glue`). -/
theorem loc_inf (v : HeightOneSpectrum (𝓞 F)) {A B : Submodule (𝓞 F) (Fin n → F)}
    (hA : A.IsLattice F) (hB : B.IsLattice F) : loc v (A ⊓ B) = loc v A ⊓ loc v B := by
  let fam : LocFamily F n :=
    { M := fun w => loc w A ⊓ loc w B
      isLattice := fun w => by
        obtain ⟨a, ha1, ha2⟩ := exists_local_bounds w (loc_isLattice w hA)
        obtain ⟨b, hb1, hb2⟩ := exists_local_bounds w (loc_isLattice w hB)
        exact isLattice_of_bounds w (k := ((max a b : ℕ) : ℤ)) (k' := -(a : ℤ))
          (le_inf ((ball_anti w (by simp)).trans ha1) ((ball_anti w (by simp)).trans hb1))
          (inf_le_left.trans ha2)
      eventually_std := by
        filter_upwards [loc_eventually_std hA, loc_eventually_std hB] with w h1 h2
        rw [h1, h2, inf_idem] }
  have hg : fam.glue = A ⊓ B := by
    ext x
    rw [LocFamily.mem_glue, Submodule.mem_inf, mem_iff_forall_loc hA, mem_iff_forall_loc hB, ← forall_and]
    rfl
  rw [← hg, fam.loc_glue]

/-- **$g(A \cap B) = gA \cap gB$** for $g \in \mathrm{GL}_n(F_\mathfrak p)$ acting on $\mathfrak o_\mathfrak p$-submodules
$A, B$ of $F_\mathfrak p^n$ (`locAct`; $g$ is injective). -/
theorem locAct_inf (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (v.adicCompletion F))
    (A B : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)) :
    locAct v g (A ⊓ B) = locAct v g A ⊓ locAct v g B := by
  unfold locAct
  refine Submodule.map_inf _ ?_
  intro x y hxy
  have h := congrArg (fun z => g⁻¹.val *ᵥ z) hxy
  simpa [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, mulVec_mulVec] using h

end General

section Rat

variable {n : ℕ}

/-- For $F = \mathbb Q$ use the library's algebra structure on $\mathbb Q_v$ (file-local, as in `Sec106Facts.lean`). -/
local instance (priority := high) t3AlgAdicQ (w : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (w.adicCompletion ℚ) := algAdic ℚ w

/-- The spot $2$ of $\mathbb Q$ exists. -/
private theorem t3_exists_two_place : ∃ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∈ v.asIdeal := by
  have hdu : ¬ IsUnit (2 : 𝓞 ℚ) := fun h => by
    have := h.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)
    rw [map_ofNat] at this
    rcases Int.isUnit_iff.1 this with h' | h' <;> norm_num at h'
  have hI : Ideal.span {(2 : 𝓞 ℚ)} ≠ ⊤ := fun h => hdu (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hI
  have hne : M ≠ ⊥ := (Ideal.bot_lt_of_maximal M (RingOfIntegers.not_isField ℚ)).ne'
  exact ⟨⟨M, hM.isPrime, hne⟩, hle (Ideal.subset_span rfl)⟩

private theorem t3_int_of (c : 𝓞 ℚ) : ∃ k : ℤ, ((k : ℤ) : 𝓞 ℚ) = c :=
  ⟨Rat.ringOfIntegersEquiv c, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
    (Rat.ringOfIntegersEquiv.symm_apply_apply c)⟩

private theorem t3_eval (x : Fin n → ℚ) : (sumSqForm n).eval x = ∑ i, x i ^ 2 := by
  rw [sumSqForm, QuadForm.eval, QuadForm.evalIn_diag]; simp

/-- A lattice on $I_n$ ($n \ge 1$) with $\mathfrak sL = \mathbb Z$ and $\mathfrak vL = \mathbb Z$ is unimodular
($L^\# = L$). ($L$ is regular since $I_n$ is positive definite.) -/
private theorem t3_isUnimodularZ_of {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) (hn : 0 < n)
    (hs : OMeara.scale (sumSqForm n).toQuadraticForm L = 1)
    (hv : OMeara.volume (sumSqForm n).toQuadraticForm L = 1) : IsUnimodularZ (sumSqForm n) L := by
  have hreg : OMeara.IsRegular (sumSqForm n).toQuadraticForm L := by
    intro x hx h0
    have h := h0 x hx
    rw [OMeara.bil_self, omeara_Q_eq, t3_eval] at h
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp h i (Finset.mem_univ i)
    simpa using this
  have hU : OMeara.IsUnimodular (sumSqForm n).toQuadraticForm L :=
    ⟨one_submodule_ne_bot, hs, by rw [hv, one_pow]⟩
  have h := (OMeara.isUnimodular_iff_dual_eq _ hL.fg (lattice_ne_bot hL hn) hreg).mp hU
  rwa [dual_eq_omearaDual _ hL] at h

variable (Q : QuadForm ℚ n)

/-- The norm of an even unimodular lattice is $2\mathbb Z$. -/
private theorem t3_normIdeal_even {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) (hn : 0 < n)
    (hu : IsUnimodularZ Q L) (he : IsEvenLat Q L) :
    OMeara.normIdeal Q.toQuadraticForm L = Submodule.span (𝓞 ℚ) {(2 : ℚ)} := by
  obtain ⟨-, hge, -, -⟩ := omeara106_r11 Q hL hn hu
  refine le_antisymm ?_ hge
  rw [OMeara.normIdeal, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨m, hm⟩ := he x hx
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  refine ⟨(m : 𝓞 ℚ), ?_⟩
  rw [omeara_Q_eq, hm, Algebra.smul_def, map_intCast]
  ring

/-- A lattice of norm $2\mathbb Z$ is even. -/
private theorem t3_even_of_normIdeal {L : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (h : OMeara.normIdeal Q.toQuadraticForm L = Submodule.span (𝓞 ℚ) {(2 : ℚ)}) : IsEvenLat Q L := by
  intro x hx
  have h1 := OMeara.Q_mem_normIdeal Q.toQuadraticForm hx
  rw [h, Submodule.mem_span_singleton] at h1
  obtain ⟨a, ha⟩ := h1
  obtain ⟨k, rfl⟩ := t3_int_of a
  refine ⟨k, ?_⟩
  rw [← omeara_Q_eq, ← ha, Algebra.smul_def, map_intCast]
  ring

/-- Unimodular lattices of the same parity have the same norm ($2\mathbb Z$ if even, $\mathbb Z$ if odd; 106.r11). -/
private theorem t3_normIdeal_eq {L M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ)
    (hM : M.IsLattice ℚ) (hn : 0 < n) (hLu : IsUnimodularZ Q L) (hMu : IsUnimodularZ Q M)
    (hpar : IsEvenLat Q L ↔ IsEvenLat Q M) :
    OMeara.normIdeal Q.toQuadraticForm L = OMeara.normIdeal Q.toQuadraticForm M := by
  by_cases he : IsEvenLat Q L
  · rw [t3_normIdeal_even Q hL hn hLu he, t3_normIdeal_even Q hM hn hMu (hpar.mp he)]
  · have h1 : OMeara.normIdeal Q.toQuadraticForm L = 1 :=
      (omeara106_r11 Q hL hn hLu).2.2.2.resolve_right fun h => he (t3_even_of_normIdeal Q h)
    have h2 : OMeara.normIdeal Q.toQuadraticForm M = 1 :=
      (omeara106_r11 Q hM hn hMu).2.2.2.resolve_right fun h => he (hpar.mpr (t3_even_of_normIdeal Q h))
    rw [h1, h2]

private theorem t3_isModularLat {L : Lat ℚ n} (hn : 0 < n) (hu : IsUnimodularZ Q L.1) :
    IsModularLat Q L :=
  ⟨1, one_ne_zero, by rw [FractionalIdeal.coe_one]; exact isUnimodular_of_isUnimodularZ Q L.2 hn hu⟩

/-- **Transfer of an adjacent pair** (the core of O'Meara's proof of 106:3, p. 326, with the dyadic classification
replaced by 93:29). Let $n \ge 1$ and let $L, M, N$ be unimodular lattices on $I_n$ (`hL`, `hM`, `hN`), with $N$
adjacent to $M$ (`hMN : Nbr.IsNbrL (sumSqForm n) 2 M.1 N.1`) and $L$ even iff $M$ is even (`hpar`). Then there is a
unimodular lattice $K$ on $I_n$, adjacent to $L$, with $K$ even iff $N$ is even.

*Proof.* $L$ and $M$ have scale $\mathbb Z$ and the same norm, so they are in one genus (93:29 and 92:2,
`sameGenus_of_isModularLat_rat`): $L_p = g_pM_p$ with $g_p \in O(V_p)$ for every $p$. Glue $K_p = g_pN_p$ (almost all
standard since $N_p = M_p$ for odd $p$, 106.r21) to a lattice $K$ (81:14). $K$ is in the genus of $N$: same scale
and volume $\mathbb Z$, hence unimodular; $K_2 = g_2N_2$ is even iff $N_2$ is, so $K$ is even iff $N$ is (106.r15).
$(K \cap L)_p = g_p(N \cap M)_p$, so $K \cap L$ is in the genus of $N \cap M$ and
$\mathfrak v(K \cap L) = \mathfrak v(N \cap M) = 4\mathbb Z$ (102.r18 and 106:5); by 106:5, $K$ is adjacent to $L$. -/
theorem exists_adjacent_of_sameParity (hn : 0 < n) {L M N : Lat ℚ n}
    (hL : IsUnimodularZ (sumSqForm n) L.1) (hM : IsUnimodularZ (sumSqForm n) M.1)
    (hN : IsUnimodularZ (sumSqForm n) N.1) (hMN : Nbr.IsNbrL (sumSqForm n) 2 M.1 N.1)
    (hpar : IsEvenLat (sumSqForm n) L.1 ↔ IsEvenLat (sumSqForm n) M.1) :
    ∃ K : Lat ℚ n, IsUnimodularZ (sumSqForm n) K.1 ∧
      (IsEvenLat (sumSqForm n) K.1 ↔ IsEvenLat (sumSqForm n) N.1) ∧
      Nbr.IsNbrL (sumSqForm n) 2 L.1 K.1 := by
  have hQ : (sumSqForm n).Nondegenerate := QuadForm.nondegenerate_diag (fun _ => one_ne_zero)
  have hs : OMeara.scale (sumSqForm n).toQuadraticForm M.1 =
      OMeara.scale (sumSqForm n).toQuadraticForm L.1 := by
    rw [(omeara106_r11 _ M.2 hn hM).1, (omeara106_r11 _ L.2 hn hL).1]
  have hnorm : OMeara.normIdeal (sumSqForm n).toQuadraticForm M.1 =
      OMeara.normIdeal (sumSqForm n).toQuadraticForm L.1 :=
    t3_normIdeal_eq _ M.2 L.2 hn hM hL hpar.symm
  have hgen : SameGenus (sumSqForm n) M.1 L.1 :=
    sameGenus_of_isModularLat_rat _ hQ (t3_isModularLat _ hn hM) (t3_isModularLat _ hn hL) hs hnorm
  choose g hg hgL using hgen
  have hNM : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ v.asIdeal → loc v N.1 = loc v M.1 :=
    (omeara106_r21 _ N M hN hMN).2
  let fam : LocFamily ℚ n :=
    { M := fun v => locAct v (g v) (loc v N.1)
      isLattice := fun v => locAct_isLattice _ (loc_isLattice v N.2)
      eventually_std := by
        filter_upwards [eventually_not_mem (two_ne_zero : (2 : 𝓞 ℚ) ≠ 0), loc_eventually_std L.2]
          with v hv hstd
        rw [hNM v hv, hgL v, hstd] }
  let J : Lat ℚ n := ⟨fam.glue, fam.glue_isLattice⟩
  have hJloc : ∀ v, loc v J.1 = locAct v (g v) (loc v N.1) := fun v => fam.loc_glue v
  have hgenNJ : SameGenus (sumSqForm n) N.1 J.1 := fun v => ⟨g v, hg v, (hJloc v).symm⟩
  have hvolJ : OMeara.volume (sumSqForm n).toQuadraticForm J.1 = 1 := by
    have := (omeara102_r18_holds (sumSqForm n)).holds N J hgenNJ
    unfold genusVolume at this
    rw [← this, volume_eq_one_of_unimodular _ N.2 hn hN]
  have hsJ : OMeara.scale (sumSqForm n).toQuadraticForm J.1 = 1 := by
    rw [← scale_eq_of_sameGenus (sumSqForm n) hgenNJ, (omeara106_r11 _ N.2 hn hN).1]
  have hJu : IsUnimodularZ (sumSqForm n) J.1 := t3_isUnimodularZ_of J.2 hn hsJ hvolJ
  obtain ⟨v2, hv2⟩ := t3_exists_two_place
  refine ⟨J, hJu, ?_, ?_⟩
  · rw [omeara106_r15 _ v2 hJu hv2, omeara106_r15 _ v2 hN hv2, hJloc v2]
    constructor
    · intro h x hx
      obtain ⟨c, hc⟩ := h ((g v2).val *ᵥ x) ⟨x, hx, rfl⟩
      exact ⟨c, by rw [locEval, ← evalIn_mulVec_of_mem _ (hg v2)]; exact hc⟩
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := mem_locAct.mp hy
      obtain ⟨c, hc⟩ := h x hx
      exact ⟨c, by rw [locEval, evalIn_mulVec_of_mem _ (hg v2)]; exact hc⟩
  · have h5NM := omeara106_5 _ N.2 M.2 hn hN hM
    have hvNM := h5NM.2.mp (h5NM.1.mp hMN)
    have h5JL := omeara106_5 _ J.2 L.2 hn hJu hL
    refine h5JL.1.mpr (h5JL.2.mpr ?_)
    have hgen2 : SameGenus (sumSqForm n) (N.1 ⊓ M.1) (J.1 ⊓ L.1) := fun v => ⟨g v, hg v, by
      rw [loc_inf v N.2 M.2, loc_inf v J.2 L.2, locAct_inf, hgL v, hJloc v]⟩
    have := (omeara102_r18_holds (sumSqForm n)).holds ⟨_, isLattice_inf N.2 M.2⟩
      ⟨_, isLattice_inf J.2 L.2⟩ hgen2
    unfold genusVolume at this
    rw [← this]
    exact hvNM

/-! ### The models: $D$, $E$ and a neighbour of each -/

private theorem t3_sumSq_bil (x y : Fin n → ℚ) : bil (sumSqForm n) x y = 2 * ∑ i, x i * y i := by
  have h : (sumSqForm n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
    · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]
  rw [bil, h, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, dotProduct, smul_eq_mul]

private theorem t3_mem_intVec {x : Fin n → ℚ} :
    x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ ∀ i, ∃ m : ℤ, x i = m := by
  rw [mem_intVec]
  refine forall_congr' fun i => ⟨?_, ?_⟩
  · rintro ⟨a, ha⟩
    obtain ⟨m, rfl⟩ := t3_int_of a
    exact ⟨m, by rw [← ha]; simp⟩
  · rintro ⟨m, hm⟩
    exact ⟨(m : 𝓞 ℚ), by rw [hm]; simp⟩

private theorem t3_isLattice_of_nbr {J L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : Nbr.IsNbrL Q 2 J L)
    (hL : L.IsLattice ℚ) : J.IsLattice ℚ := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hL
  refine isLattice_of_global_bounds (d := 2 * d) (mul_ne_zero two_ne_zero hd) (fun x hx => ?_)
    (fun x hx => ?_)
  · have := h.smul_left _ (h1 x hx)
    rw [algebraMap_smul] at this
    rwa [mul_smul]
  · have := h.smul_right x hx
    rw [algebraMap_smul] at this
    rw [mul_comm, mul_smul]
    exact h2 _ this

/-- 106:7 as a lattice: $K = \mathbb Zy + (\mathbb Zy + M)^\#$ is a unimodular lattice adjacent to $M$. -/
private theorem t3_nbr7 {M : Lat ℚ n} (hM : IsUnimodularZ Q M.1) {y : Fin n → ℚ}
    (h2 : (2 : ℚ) • y ∈ M.1) (hy : y ∉ M.1) (hQy : ∃ m : ℤ, Q.eval y = m) :
    ∃ K : Lat ℚ n, K.1 = Submodule.span (𝓞 ℚ) {y} ⊔ omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ M.1) ∧
      IsUnimodularZ Q K.1 ∧ Nbr.IsNbrL Q 2 M.1 K.1 := by
  obtain ⟨hu, -, hadj, -⟩ := omeara106_7 Q hM h2 hy hQy
  exact ⟨⟨_, t3_isLattice_of_nbr Q hadj M.2⟩, rfl, hu, hadj.symm⟩

/-- $D = \mathbb Z^n$ is odd ($Q(x_0) = 1$). -/
private theorem t3_intVec_odd (hn : 0 < n) :
    ¬ IsEvenLat (sumSqForm n) (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
  intro he
  have hmem : (Pi.single ⟨0, hn⟩ (1 : ℚ) : Fin n → ℚ) ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) :=
    t3_mem_intVec.mpr fun i => by
      by_cases h : i = ⟨0, hn⟩
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩
  obtain ⟨m, hm⟩ := he _ hmem
  rw [t3_eval] at hm
  simp [Pi.single_apply] at hm
  have : (2 : ℤ) * m = 1 := by exact_mod_cast hm.symm
  omega

/-- **An odd unimodular lattice adjacent to $D = \mathbb Z^n$** ($n \ge 5$): the neighbour through
$y = \tfrac12(x_0 + x_1 + x_2 + x_3)$ (106:7, $Q(y) = 1$); it contains $x_4$, of norm $1$. -/
private theorem t3_oddNbr_D (h5 : 5 ≤ n) : ∃ K : Lat ℚ n, IsUnimodularZ (sumSqForm n) K.1 ∧
    ¬ IsEvenLat (sumSqForm n) K.1 ∧
    Nbr.IsNbrL (sumSqForm n) 2 (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) K.1 := by
  set y : Fin n → ℚ := fun i => if i.val < 4 then 1 / 2 else 0 with hy
  have h2 : (2 : ℚ) • y ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := t3_mem_intVec.mpr fun i => by
    by_cases h : i.val < 4
    · exact ⟨1, by simp [hy, h]⟩
    · exact ⟨0, by simp [hy, h]⟩
  have hyD : y ∉ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := fun h => by
    obtain ⟨m, hm⟩ := t3_mem_intVec.mp h ⟨0, by omega⟩
    simp [hy] at hm
    have h1 : (2 : ℚ) * m = 1 := by rw [← hm]; norm_num
    have h2 : 2 * m = 1 := by exact_mod_cast h1
    omega
  have hQy : (sumSqForm n).eval y = 1 := by
    rw [t3_eval]
    set f : ℕ → ℚ := fun k => if k < 4 then 1 / 4 else 0 with hf
    have hyf : ∀ i : Fin n, y i ^ 2 = f i.val := fun i => by
      by_cases h : i.val < 4 <;> simp [hy, hf, h]
      norm_num
    rw [Finset.sum_congr rfl (fun i _ => hyf i), Fin.sum_univ_eq_sum_range f n]
    obtain ⟨k, rfl⟩ : ∃ k, n = 4 + k := ⟨n - 4, by omega⟩
    rw [Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range k) (fun x _ => by simp [hf])]
    simp [Finset.sum_range_succ, hf]
    norm_num
  obtain ⟨K, hK, hu, hadj⟩ := t3_nbr7 (sumSqForm n) (M := ⟨intVec, intVec_isLattice⟩)
    adj_D_unimodular h2 hyD ⟨1, by rw [hQy]; simp⟩
  refine ⟨K, hu, fun he => ?_, hadj⟩
  set j : Fin n := ⟨4, by omega⟩ with hj
  have hjy : y j = 0 := by simp [hy, hj]
  have heK : (Pi.single j (1 : ℚ) : Fin n → ℚ) ∈ K.1 := by
    rw [hK]
    refine Submodule.mem_sup_right ?_
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨m, hm⟩ := t3_mem_intVec.mp hb j
    obtain ⟨k, hk⟩ := exists_int_smul_eq c y
    refine ⟨m, ?_⟩
    rw [t3_sumSq_bil, hk]
    simp [Pi.single_apply, hjy, hm]
  obtain ⟨m, hm⟩ := he _ heK
  rw [t3_eval] at hm
  simp [Pi.single_apply] at hm
  have : (2 : ℤ) * m = 1 := by exact_mod_cast hm.symm
  omega

/-- **An even unimodular lattice adjacent to $E$** ($8 \mid n$): the neighbour through
$y = \tfrac12(x_0 + \dots + x_{n-2} - x_{n-1})$ (106:7: $2y \in E$, $y \notin E$ since $\sum y_i = n/2 - 1$ is odd,
$Q(y) = n/4$ is even); it is even because $E$ is even, $Q(y) \in 2\mathbb Z$ and $B(y, (\mathbb Zy + E)^\#) \subseteq
\mathbb Z$. -/
private theorem t3_evenNbr_E (h8n : 8 ∣ n) (h8 : 8 ≤ n) : ∃ K : Lat ℚ n, IsUnimodularZ (sumSqForm n) K.1 ∧
    IsEvenLat (sumSqForm n) K.1 ∧ Nbr.IsNbrL (sumSqForm n) 2 (omearaE n) K.1 := by
  have hn : 0 < n := by omega
  have h4 : 4 ∣ n := dvd_trans (by norm_num) h8n
  obtain ⟨k, hk⟩ := id h8n
  have hnk : (n : ℚ) = 8 * k := by rw [hk]; push_cast; ring
  obtain ⟨hEu, -, hED⟩ := omeara106_r29_adjacent h4 h8
  set last : Fin n := ⟨n - 1, by omega⟩ with hlast
  set y : Fin n → ℚ := fun i => if i = last then -1 / 2 else 1 / 2 with hy
  have hy' : ∀ i, y i = 1 / 2 - (if i = last then 1 else 0) := fun i => by
    by_cases h : i = last <;> simp [hy, h]; norm_num
  have hsum : ∑ i, y i = (n : ℚ) / 2 - 1 := by
    simp only [hy', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, nsmul_eq_mul]
    ring
  have hsq : ∀ i, y i ^ 2 = 1 / 4 := fun i => by
    by_cases h : i = last <;> simp [hy, h] <;> norm_num
  have hQy : (sumSqForm n).eval y = 2 * k := by
    rw [t3_eval, Finset.sum_congr rfl (fun i _ => hsq i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hk]
    push_cast
    ring
  set a : Fin n → ℤ := fun i => if i = last then -1 else 1 with ha
  have h2a : ∀ i, ((2 : ℚ) • y) i = a i := fun i => by
    by_cases h : i = last
    · simp [hy, ha, h]; norm_num
    · simp [hy, ha, h]
  have h2 : (2 : ℚ) • y ∈ omearaE n := by
    rw [omeara106_11 h4 hn]
    refine ⟨fun i => ⟨2 * a i, by rw [h2a]; push_cast; ring⟩,
      fun i j => ⟨a i - a j, by rw [h2a, h2a]; push_cast; ring⟩, ⟨4 * k - 1, ?_⟩⟩
    have : ∑ i, ((2 : ℚ) • y) i = 2 * ∑ i, y i := by
      rw [Finset.mul_sum]; rfl
    rw [this, hsum, hk]
    push_cast
    ring
  have hyE : y ∉ omearaE n := by
    rw [omeara106_11 h4 hn]
    rintro ⟨-, -, m, hm⟩
    rw [hsum, hk] at hm
    have h1 : ((4 * k - 1 : ℤ) : ℚ) = ((2 * m : ℤ) : ℚ) := by push_cast; push_cast at hm; linarith
    have h2 : 4 * k - 1 = 2 * m := by exact_mod_cast h1
    omega
  obtain ⟨K, hK, hu, hadj⟩ := t3_nbr7 (sumSqForm n)
    (M := ⟨omearaE n, t3_isLattice_of_nbr _ hED intVec_isLattice⟩)
    hEu h2 hyE ⟨2 * k, by rw [hQy]; push_cast; ring⟩
  refine ⟨K, hu, ?_, hadj⟩
  intro x hx
  rw [hK] at hx
  obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
  obtain ⟨t, ht⟩ := exists_int_smul_eq c y
  have hzE : z ∈ omearaE n := by
    have : z ∈ omearaDual (sumSqForm n) (omearaE n) := fun w hw =>
      hz w (Submodule.mem_sup_right hw)
    rwa [hEu] at this
  obtain ⟨m1, hm1⟩ := omearaE_even h8n h8 z hzE
  obtain ⟨m2, hm2⟩ := hz y (Submodule.mem_sup_left (Submodule.mem_span_singleton_self y))
  rw [t3_sumSq_bil] at hm2
  rw [t3_eval] at hm1
  refine ⟨t ^ 2 * k + m1 + t * m2, ?_⟩
  rw [ht, t3_eval]
  have e : ∀ i, (((t : ℚ) • y + z) i) ^ 2 = (t : ℚ) ^ 2 * y i ^ 2 + z i ^ 2 + 2 * t * (z i * y i) :=
    fun i => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hsq i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm1, hnk]
  have : ∑ i, z i * y i = m2 := by linarith
  rw [this]
  push_cast
  ring

end Rat

/-- **Proposition 106:3** (O'Meara 1973, §106B, p. 326). Let $n > 0$ with $8 \mid n$ and let $L$ be a unimodular
lattice on $V = I_n$ over $\mathbb Q$ (`IsUnimodularZ (sumSqForm n) L.1`: $L^\# = L$ for $Q = x_0^2 + \dots + x_{n-1}^2$).
Then there are an even unimodular lattice $K$ ($Q(K) \subseteq 2\mathbb Z$, `IsEvenLat`) and an odd unimodular lattice
$K'$ on $V$, both adjacent to $L$ (`Nbr.IsNbrL (sumSqForm n) 2 L.1 _`). This is the named statement `OMeara106_3`.
Unconditional.

*A different proof from the book.* O'Meara takes the local lattice $K_2$ of the wanted parity with invariant factors
$\tfrac12, 1, \dots, 1, 2$ in $L_2$ from the dyadic classification (93:18) and glues it with the $L_p$ ($p$ odd). Here
$L$ is compared with a model of its parity ($D = \mathbb Z^n$ if $L$ is odd, $E$ if $L$ is even), which has unimodular
neighbours of both parities ($E$ and a neighbour through $\tfrac12(x_0 + x_1 + x_2 + x_3)$ for $D$; $D$ and a
neighbour through $\tfrac12(x_0 + \dots + x_{n-2} - x_{n-1})$ for $E$), and the neighbour is transported to $L$ through
the genus (`exists_adjacent_of_sameParity`: 93:29, 81:14, 106.r15, 106:5). -/
@[kb "omeara1963" "§106B, 106:3, p. 326"]
theorem omeara106_3_holds : OMeara106_3 := by
  refine ⟨fun n hn h8n L hL => ?_⟩
  have h8 : 8 ≤ n := Nat.le_of_dvd hn h8n
  have h4 : 4 ∣ n := dvd_trans (by norm_num) h8n
  obtain ⟨hEu, -, hED⟩ := omeara106_r29_adjacent h4 h8
  let D : Lat ℚ n := ⟨intVec, intVec_isLattice⟩
  let E : Lat ℚ n := ⟨omearaE n, t3_isLattice_of_nbr _ hED intVec_isLattice⟩
  have hEe : IsEvenLat (sumSqForm n) E.1 := omearaE_even h8n h8
  have hDo : ¬ IsEvenLat (sumSqForm n) D.1 := t3_intVec_odd hn
  have hDu : IsUnimodularZ (sumSqForm n) D.1 := adj_D_unimodular
  obtain ⟨ND, hNDu, hNDo, hDND⟩ := t3_oddNbr_D (n := n) (by omega)
  obtain ⟨NE, hNEu, hNEe, hENE⟩ := t3_evenNbr_E h8n h8
  by_cases hLe : IsEvenLat (sumSqForm n) L.1
  · have hpar : IsEvenLat (sumSqForm n) L.1 ↔ IsEvenLat (sumSqForm n) E.1 := iff_of_true hLe hEe
    obtain ⟨K1, hK1u, hK1p, hK1a⟩ := exists_adjacent_of_sameParity (N := NE) hn hL hEu hNEu hENE hpar
    obtain ⟨K2, hK2u, hK2p, hK2a⟩ := exists_adjacent_of_sameParity (N := D) hn hL hEu hDu hED hpar
    exact ⟨⟨K1, hK1u, hK1p.mpr hNEe, hK1a⟩, ⟨K2, hK2u, fun h => hDo (hK2p.mp h), hK2a⟩⟩
  · have hpar : IsEvenLat (sumSqForm n) L.1 ↔ IsEvenLat (sumSqForm n) D.1 := iff_of_false hLe hDo
    obtain ⟨K1, hK1u, hK1p, hK1a⟩ := exists_adjacent_of_sameParity (N := E) hn hL hDu hEu hED.symm hpar
    obtain ⟨K2, hK2u, hK2p, hK2a⟩ := exists_adjacent_of_sameParity (N := ND) hn hL hDu hNDu hDND hpar
    exact ⟨⟨K1, hK1u, hK1p.mpr hEe, hK1a⟩, ⟨K2, hK2u, fun h => hNDo (hK2p.mp h), hK2a⟩⟩

end QuadFormsKB.Lattices
