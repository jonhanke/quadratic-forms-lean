/-
# $\theta_Q - \theta_{Q'}$ is a cusp form for $Q'$ in the genus of $Q$ (part A)

For a positive definite integral form $Q$ in $n = 2k$ variables and $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in
\mathrm{SL}_2(\mathbb{Z})$ with $c \ge 1$, the expansion of $\Theta_Q$ at the cusp $a/c$ (`thetaGram_cusp`) gives
$$(\Theta_Q \mid_k \gamma)(\tau) \longrightarrow M_A(a, c) = \Big(\frac{-i}{2c}\Big)^k(\det A)^{-1/2}\,G_A(a, c)
\qquad (\operatorname{Im}\tau \to \infty),$$
`thetaMult`, with $G_A(a, c) = \sum_{\vec{r} \bmod c} e(a\,Q(\vec{r})/c)$ and $A = H/2$ the Gram matrix
(`tendsto_theta_cusp`). This file proves:

* **Genus invariance of the cusp data** (`SameGenus.thetaMult_eq`): if $Q'$ is in the genus of $Q$ (`SameGenus`), then
  $\det H = \det H'$ (`SameGenus.det_hessian_eq`) and $G_A(a, c) = G_{A'}(a, c)$ for all $a$ and $c \ge 1$
  (`SameGenus.gaussSum_eq`). *Proof:* the local equivalences $g_p \in \mathrm{GL}_n(\mathbb{Z}_p)$ reduce to
  $\mathrm{GL}_n(\mathbb{Z}/p^e)$ and glue by the Chinese remainder theorem (`ZMod.equivPi`) to
  $\bar g \in \mathrm{GL}_n(\mathbb{Z}/c)$ with $Q(\bar g\vec{x}) = Q'(\vec{x})$ on $(\mathbb{Z}/c)^n$
  (`SameGenus.isometricGL_zmod`); the substitution $\vec{r} \mapsto \bar g\vec{r}$ permutes $(\mathbb{Z}/c)^n$.
* **Cuspidality** (`isZeroAtImInfty_theta_sub_slash`): $(\Theta_Q - \Theta_{Q'}) \mid_k \gamma \to 0$ at $i\infty$ for every
  $\gamma \in \mathrm{SL}_2(\mathbb{Z})$; hence $\Theta_Q - \Theta_{Q'} \in S_k(\Gamma_1(N))$ (`thetaCuspDiff`, Mathlib's
  `CuspForm`) for $N$ a common level, transforming with $\chi_Q$ under $\Gamma_0(N)$ (`thetaCuspDiff_slash_gamma0`).
* **The genus theta series** $\Theta_{\mathrm{Gen}(Q)} = \mathrm{Mass}(Q)^{-1}\sum_{[Q'] \in \mathrm{Gen}(Q)}\Theta_{Q'}/|\mathrm{Aut}(Q')|$
  (`thetaGen`), with $q$-expansion $\sum_{m \ge 0}a_E(m)e(mz)$ (`hasSum_thetaGen`), and the cusp form
  $\Theta_Q - \Theta_{\mathrm{Gen}(Q)} \in S_k(\Gamma_1(N))$ (`thetaGenCusp`), under `GenusFinite`.

Sources: Iwaniec, *Topics in Classical Automorphic Forms*, §10.3–10.4 [unverified]; Hanke 2004, §4, (4.3)–(4.5),
pp. 365–366 ("$E$ = the genus theta series, $f = \Theta_Q - E$ cuspidal") [unverified]; Siegel 1935 [unverified].
-/
import QuadFormsKB.Siegel.ThetaCharacter
import QuadFormsKB.Siegel.Mass

open Complex Matrix Filter Topology
open QuadFormsKB.Analysis (quadAt quadAtR)
open ModularForm
open scoped MatrixGroups

namespace QuadFormsKB.Siegel

noncomputable section

variable {n : ℕ}

/-! ### Base change of forms and of equivalences -/

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring homomorphism commutes with evaluation: $f(Q(\vec{x})) = (f_*Q)(f(\vec{x}))$. -/
theorem map_eval_eq (f : R →+* S) (Q : QuadForm R n) (x : Fin n → R) :
    f (Q.eval x) = (Q.map f).eval (fun i => f (x i)) := by
  simp [QuadForm.evalIn, QuadForm.map, map_sum, apply_ite]

/-- Base change of an integral form is transitive: $f_*(\iota_{R*}Q) = \iota_{S*}Q$. -/
theorem map_map_int (f : R →+* S) (Q : QuadForm ℤ n) :
    (Q.map (Int.castRingHom R)).map f = Q.map (Int.castRingHom S) := by
  ext i j; simp [QuadForm.map]

/-- **Equivalence base-changes along a surjective ring homomorphism** $f : R \to S$: if $Q(g\vec{x}) = Q'(\vec{x})$ on
$R^n$ then $(f_*Q)(f(g)\vec{x}) = (f_*Q')(\vec{x})$ on $S^n$. -/
theorem IsometricGL.map_of_surjective (f : R →+* S) (hf : Function.Surjective f) {Q Q' : QuadForm R n}
    (h : IsometricGL Q Q') : IsometricGL (Q.map f) (Q'.map f) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨Units.map (RingHom.mapMatrix (m := Fin n) f).toMonoidHom g, fun x => ?_⟩
  have e : ((Units.map (RingHom.mapMatrix (m := Fin n) f).toMonoidHom g : GL (Fin n) S) :
      Matrix (Fin n) (Fin n) S) = g.val.map f := rfl
  rw [e]
  choose y hy using fun i => hf (x i)
  have hx : x = fun i => f (y i) := funext fun i => (hy i).symm
  rw [hx, show (g.val.map f *ᵥ fun i => f (y i)) = fun i => f ((g.val *ᵥ y) i) from
    funext fun i => (RingHom.map_mulVec f g.val y i).symm, ← map_eval_eq, ← map_eval_eq, hg]

/-- **Equivalences glue over a product of rings.** -/
theorem IsometricGL.pi {ι : Type*} {T : ι → Type*} [∀ i, CommRing (T i)] {Q Q' : QuadForm ℤ n}
    (h : ∀ i, IsometricGL (Q.map (Int.castRingHom (T i))) (Q'.map (Int.castRingHom (T i)))) :
    IsometricGL (Q.map (Int.castRingHom (∀ i, T i))) (Q'.map (Int.castRingHom (∀ i, T i))) := by
  choose g hg using h
  set G : Matrix (Fin n) (Fin n) (∀ i, T i) := Matrix.of fun a b i => (g i).val a b with hG
  set Gi : Matrix (Fin n) (Fin n) (∀ i, T i) := Matrix.of fun a b i => (g i)⁻¹.val a b with hGi
  have hmap : ∀ (M : ∀ j, Matrix (Fin n) (Fin n) (T j)) (i : ι),
      (Matrix.of fun a b j => M j a b : Matrix (Fin n) (Fin n) (∀ i, T i)).map (Pi.evalRingHom T i) =
        M i := fun M i => by ext a b; rfl
  have hinj : ∀ M M' : Matrix (Fin n) (Fin n) (∀ i, T i),
      (∀ i, M.map (Pi.evalRingHom T i) = M'.map (Pi.evalRingHom T i)) → M = M' := by
    intro M M' hM
    ext a b i
    have := congrFun (congrFun (hM i) a) b
    simpa using this
  have h1 : G * Gi = 1 := hinj _ _ fun i => by
    rw [Matrix.map_mul, hG, hGi, hmap (fun j => (g j).val), hmap (fun j => (g j)⁻¹.val),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : Gi * G = 1 := hinj _ _ fun i => by
    rw [Matrix.map_mul, hG, hGi, hmap (fun j => (g j).val), hmap (fun j => (g j)⁻¹.val),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨G, Gi, h1, h2⟩, fun x => ?_⟩
  change (Q.map (Int.castRingHom (∀ i, T i))).eval (G *ᵥ x) = _
  funext i
  have e1 := map_eval_eq (Pi.evalRingHom T i) (Q.map (Int.castRingHom (∀ i, T i))) (G *ᵥ x)
  have e2 := map_eval_eq (Pi.evalRingHom T i) (Q'.map (Int.castRingHom (∀ i, T i))) x
  rw [map_map_int] at e1 e2
  have e3 : (fun a => Pi.evalRingHom T i ((G *ᵥ x) a)) =
      (g i).val *ᵥ (fun a => Pi.evalRingHom T i (x a)) := by
    funext a
    rw [RingHom.map_mulVec, hG, hmap (fun j => (g j).val)]; rfl
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [e3]
  exact hg i _

/-- The Hessian of a base change is the base change of the Hessian. -/
theorem hessian_map (f : R →+* S) (Q : QuadForm R n) : (Q.map f).hessian = Q.hessian.map f := by
  simp [QuadForm.hessian, QuadForm.map, Matrix.map_add _ (map_add f), Matrix.transpose_map]

/-- **Equivalent forms have congruent Hessians** over any commutative ring: $Q(g\vec{x}) = Q'(\vec{x})$ on $S^n$
implies $g^{\mathsf T}Hg = H'$ (polarization `QuadForm.polar_eq_hessian`; no division by $2$). -/
theorem IsometricGL.hessian_eq {Q Q' : QuadForm S n} (h : IsometricGL Q Q') :
    ∃ g : GL (Fin n) S, g.valᵀ * Q.hessian * g.val = Q'.hessian := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  have hid : ∀ M : Matrix (Fin n) (Fin n) S, M.map (algebraMap S S) = M := fun M => by
    ext; simp
  have key : ∀ x y : Fin n → S, x ⬝ᵥ ((g.valᵀ * Q.hessian * g.val) *ᵥ y) = x ⬝ᵥ (Q'.hessian *ᵥ y) := by
    intro x y
    have hp := QuadForm.polar_eq_hessian S Q (g.val *ᵥ x) (g.val *ᵥ y)
    have hp' := QuadForm.polar_eq_hessian S Q' x y
    rw [hid] at hp hp'
    calc x ⬝ᵥ ((g.valᵀ * Q.hessian * g.val) *ᵥ y) = (g.val *ᵥ x) ⬝ᵥ (Q.hessian *ᵥ (g.val *ᵥ y)) := by
          rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
      _ = Q.eval (g.val *ᵥ x + g.val *ᵥ y) - Q.eval (g.val *ᵥ x) - Q.eval (g.val *ᵥ y) := hp.symm
      _ = Q'.eval (x + y) - Q'.eval x - Q'.eval y := by rw [← mulVec_add, hg, hg, hg]
      _ = _ := hp'
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  simpa [mulVec_single_one, single_one_dotProduct] using this

end BaseChange

/-! ### From the genus to equivalence modulo $c$ -/

variable {Q Q' : QuadForm ℤ n}

/-- Every ring homomorphism onto $\mathbb{Z}/m$ is surjective. -/
lemma surjective_to_zmod {R : Type*} [CommRing R] {m : ℕ} (f : R →+* ZMod m) : Function.Surjective f :=
  fun x => ⟨((ZMod.cast x : ℤ) : R), by rw [map_intCast, ZMod.intCast_zmod_cast]⟩

/-- **Forms in one genus are equivalent modulo every $c \ge 1$:** there is $\bar g \in \mathrm{GL}_n(\mathbb{Z}/c)$ with
$Q(\bar g\vec{x}) = Q'(\vec{x})$ for all $\vec{x} \in (\mathbb{Z}/c)^n$. *Proof:* reduce $g_p \in \mathrm{GL}_n(\mathbb{Z}_p)$
modulo $p^{e_p}$ (`PadicInt.toZModPow`) and glue by CRT (`ZMod.equivPi`, `IsometricGL.pi`). -/
@[kb "cassels1978" "Ch. 9, §1 (genus and congruences) [unverified]"]
theorem SameGenus.isometricGL_zmod (h : SameGenus Q Q') {c : ℕ} (hc : c ≠ 0) :
    IsometricGL (Q.map (Int.castRingHom (ZMod c))) (Q'.map (Int.castRingHom (ZMod c))) := by
  have hloc : ∀ p : c.primeFactors, IsometricGL
      (Q.map (Int.castRingHom (ZMod ((p : ℕ) ^ c.factorization p))))
      (Q'.map (Int.castRingHom (ZMod ((p : ℕ) ^ c.factorization p)))) := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    have := (h.1 p).map_of_surjective (PadicInt.toZModPow (c.factorization p))
      (surjective_to_zmod _)
    rwa [map_map_int, map_map_int] at this
  have hpi := IsometricGL.pi hloc
  have := hpi.map_of_surjective (ZMod.equivPi c hc).symm.toRingHom
    (ZMod.equivPi c hc).symm.surjective
  rwa [map_map_int, map_map_int] at this

/-! ### Genus invariance of the cusp data -/

/-- **The Gauss sum of $Q$ modulo $c$ as a character sum over $(\mathbb{Z}/c)^n$:**
$G_A(a, \vec 0, c) = \sum_{\vec{r} \in (\mathbb{Z}/c)^n}\psi\big(a\,\bar Q(\vec{r})\big)$, $\psi$ = `ZMod.stdAddChar`,
$\bar Q$ the reduction of $Q$ modulo $c$. -/
theorem gaussSum_gramMatrix_eq (Q : QuadForm ℤ n) (a : ℤ) (c : ℕ) [NeZero c] :
    gaussSum (gramMatrix Q) a c 0 = ∑ r : Fin n → ZMod c,
      ZMod.stdAddChar ((a : ZMod c) * (Q.map (Int.castRingHom (ZMod c))).eval r) := by
  unfold gaussSum
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : r = fun i => Int.castRingHom (ZMod c) (liftZ r i) := by
    funext i; simp [liftZ]
  have hq : (Q.map (Int.castRingHom (ZMod c))).eval r = ((Q.eval (liftZ r) : ℤ) : ZMod c) := by
    conv_lhs => rw [hr]
    rw [← map_eval_eq]; rfl
  rw [hq, ← Int.cast_mul, ZMod.stdAddChar_coe, quadAt_gramMatrix]
  congr 1
  simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
  push_cast; ring

/-- **Equivalent forms modulo $c$ have equal Gauss sums:** substitute $\vec{r} \mapsto \bar g\vec{r}$. -/
theorem gaussSum_eq_of_isometricGL_zmod {c : ℕ} [NeZero c]
    (h : IsometricGL (Q.map (Int.castRingHom (ZMod c))) (Q'.map (Int.castRingHom (ZMod c)))) (a : ℤ) :
    gaussSum (gramMatrix Q) a c 0 = gaussSum (gramMatrix Q') a c 0 := by
  obtain ⟨g, hg⟩ := h
  rw [gaussSum_gramMatrix_eq, gaussSum_gramMatrix_eq]
  let e : (Fin n → ZMod c) ≃ (Fin n → ZMod c) :=
    { toFun := fun r => g.val *ᵥ r
      invFun := fun r => (g⁻¹).val *ᵥ r
      left_inv := fun r => by
        simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      right_inv := fun r => by
        simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] }
  exact (Fintype.sum_equiv e _ _ fun r => by simp only [e, Equiv.coe_fn_mk, hg]).symm

/-- **Gauss sums are genus invariants:** $G_A(a, c) = G_{A'}(a, c)$ for $Q'$ in the genus of $Q$, every
$a \in \mathbb{Z}$ and $c \ge 1$. -/
@[kb "iwaniec1997" "§10.4, Gauss sums of a genus [unverified]"]
theorem SameGenus.gaussSum_eq (h : SameGenus Q Q') (a : ℤ) (c : ℕ) [NeZero c] :
    gaussSum (gramMatrix Q) a c 0 = gaussSum (gramMatrix Q') a c 0 :=
  gaussSum_eq_of_isometricGL_zmod (h.isometricGL_zmod (NeZero.ne c)) a

/-- $\det H \bmod c$ changes by a unit square under equivalence modulo $c$. -/
lemma det_hessian_zmod (h : SameGenus Q Q') {c : ℕ} (hc : c ≠ 0) :
    ∃ u : ZMod c, IsUnit u ∧ ((Q'.hessian.det : ℤ) : ZMod c) = u ^ 2 * (Q.hessian.det : ZMod c) := by
  obtain ⟨g, hg⟩ := (h.isometricGL_zmod hc).hessian_eq
  refine ⟨g.val.det, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, ?_⟩
  have hd := congrArg Matrix.det hg
  rw [hessian_map, hessian_map, det_mul, det_mul, det_transpose] at hd
  have e : ∀ M : Matrix (Fin n) (Fin n) ℤ, (M.map (Int.castRingHom (ZMod c))).det = (M.det : ZMod c) :=
    fun M => by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [e, e] at hd
  rw [← hd]; ring

/-- $\det H > 0$ for $Q$ positive definite. -/
lemma det_hessian_pos {Q : IntQF n} (hQ : Q.PosDef) : 0 < Q.hessian.det := by
  have h := (gramMatrix_posDef hQ).det_pos
  have e : (gramMatrix Q).det = (1 / 2 : ℝ) ^ n * (Q.hessian.det : ℝ) := by
    rw [gramMatrix, det_smul, Fintype.card_fin, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [e] at h
  have : (0 : ℝ) < Q.hessian.det := pos_of_mul_pos_right h (by positivity)
  exact_mod_cast this

/-- **$\det H$ is a genus invariant** (for positive definite forms): $\det H = \det H'$. *Proof:* modulo $c = \det H$
and $c = \det H'$, $\det H' \equiv u^2\det H$ with $u$ a unit, so each divides the other. -/
@[kb "cassels1978" "Ch. 9, §1 (the determinant is a genus invariant) [unverified]"]
theorem SameGenus.det_hessian_eq {Q Q' : IntQF n} (hQ : Q.PosDef) (h : SameGenus Q Q') :
    Q.hessian.det = Q'.hessian.det := by
  have hQ' := h.posDef hQ
  have hD := det_hessian_pos hQ
  have hD' := det_hessian_pos hQ'
  have hdvd : ∀ {c : ℕ}, (c : ℤ) ∣ Q.hessian.det ∨ (c : ℤ) ∣ Q'.hessian.det → c ≠ 0 →
      ((c : ℤ) ∣ Q.hessian.det ↔ (c : ℤ) ∣ Q'.hessian.det) := by
    intro c _ hc
    obtain ⟨u, hu, he⟩ := det_hessian_zmod h hc
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, he]
    constructor
    · intro h0; rw [h0, mul_zero]
    · intro h0; exact (hu.pow 2).mul_right_eq_zero.mp h0
  have h1 : Q.hessian.det ∣ Q'.hessian.det := by
    have := (hdvd (c := Q.hessian.det.natAbs) (Or.inl (by simp)) (by omega)).mp (by simp)
    simpa using this
  have h2 : Q'.hessian.det ∣ Q.hessian.det := by
    have := (hdvd (c := Q'.hessian.det.natAbs) (Or.inr (by simp)) (by omega)).mpr (by simp)
    simpa using this
  exact Int.dvd_antisymm hD.le hD'.le h1 h2

/-- $\det A = 2^{-n}\det H$ for the Gram matrix. -/
lemma det_gramMatrix (Q : QuadForm ℤ n) : (gramMatrix Q).det = (1 / 2 : ℝ) ^ n * (Q.hessian.det : ℝ) := by
  rw [gramMatrix, det_smul, Fintype.card_fin, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl

/-- **The constant term of $\Theta_Q$ at every cusp is a genus invariant:** $M_A(a, c) = M_{A'}(a, c)$ (`thetaMult`)
for $Q'$ in the genus of $Q$, all $a \in \mathbb{Z}$, $c \ge 1$. -/
@[kb "iwaniec1997" "§10.4 [unverified]"]
theorem SameGenus.thetaMult_eq {Q Q' : IntQF n} (hQ : Q.PosDef) (h : SameGenus Q Q') (k : ℕ) (a : ℤ)
    (c : ℕ) [NeZero c] : thetaMult (gramMatrix Q) k a c = thetaMult (gramMatrix Q') k a c := by
  unfold thetaMult
  rw [det_gramMatrix, det_gramMatrix, h.det_hessian_eq hQ, h.gaussSum_eq]

/-! ### The constant term of $\Theta_Q \mid_k \gamma$ -/

/-- **Constant term of a theta-type series**, along any filter: for $P$ positive definite, $g$ bounded and
$\operatorname{Im} W \to \infty$, $\sum_{\vec{m}} g(\vec{m})\,e\big(W P[\vec{m}]\big) \to g(\vec 0)$ (as `tendsto_tsum_cexp_quad`). -/
lemma tendsto_tsum_cexp_quad_filter {α : Type*} {l : Filter α} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef)
    (g : (Fin n → ℤ) → ℂ) {B : ℝ} (hg : ∀ m, ‖g m‖ ≤ B) {W : α → ℂ}
    (hW : Tendsto (fun t => (W t).im) l atTop) :
    Tendsto (fun t => ∑' m : Fin n → ℤ, g m * cexp (2 * Real.pi * I * W t * (quadAt P m : ℂ)))
      l (𝓝 (g 0)) := by
  have hsumI := (summable_thetaGram_term hP (z := I) (by simp))
  have hlim : ∀ m : Fin n → ℤ, Tendsto (fun t => g m * cexp (2 * Real.pi * I * W t * (quadAt P m : ℂ)))
      l (𝓝 (if m = 0 then g 0 else 0)) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      have : quadAt P (0 : Fin n → ℤ) = 0 := by simp [quadAt]
      simpa [this] using tendsto_const_nhds
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hm)]
      have hpos : 0 < quadAt P m := by
        have hv : (fun i => (m i : ℝ)) ≠ 0 := by
          intro h; apply hm; funext i; have := congrFun h i; simpa using this
        simpa using hP.dotProduct_mulVec_pos hv
      rw [show (0 : ℂ) = g m * 0 by ring]
      refine Tendsto.const_mul _ ?_
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : ∀ t, ‖cexp (2 * Real.pi * I * W t * (quadAt P m : ℂ))‖ =
          Real.exp (-(2 * Real.pi * quadAt P m) * (W t).im) := by
        intro t; rw [Complex.norm_exp]; congr 1; simp [mul_re, mul_im]; ring
      simp_rw [hnorm]
      exact Real.tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (by have := Real.pi_pos; nlinarith) hW)
  have hbound : ∀ᶠ t in l, ∀ m : Fin n → ℤ,
      ‖g m * cexp (2 * Real.pi * I * W t * (quadAt P m : ℂ))‖ ≤
        B * ‖cexp (2 * Real.pi * I * I * (quadAt P m : ℂ))‖ := by
    filter_upwards [hW.eventually_ge_atTop 1] with t ht m
    rw [norm_mul]
    exact mul_le_mul (hg m) (norm_cexp_quad_le hP ht m) (norm_nonneg _)
      ((norm_nonneg _).trans (hg 0))
  have h := tendsto_tsum_of_dominated_convergence (hsumI.mul_left B) hlim hbound
  rwa [tsum_ite_eq] at h

lemma tendsto_im_atImInfty : Tendsto (fun τ : UpperHalfPlane => τ.im) UpperHalfPlane.atImInfty atTop :=
  tendsto_comap

/-- **$\Theta_Q \to 1$ at $i\infty$** (the constant term $r_Q(0) = 1$). -/
theorem tendsto_theta_atImInfty {Q : IntQF n} (hQ : Q.PosDef) :
    Tendsto (fun τ : UpperHalfPlane => theta Q τ) UpperHalfPlane.atImInfty (𝓝 1) := by
  have h := tendsto_tsum_cexp_quad_filter (gramMatrix_posDef hQ) (fun _ => (1 : ℂ)) (B := 1)
    (fun _ => by simp) (W := fun τ : UpperHalfPlane => (τ : ℂ)) tendsto_im_atImInfty
  refine h.congr fun τ => ?_
  simp [theta, quadAt_gramMatrix]

/-- **The constant term of $\Theta_Q$ at the cusp $a/c$** ($n = 2k$, $c \ge 1$, $ad - bc = 1$): as
$\operatorname{Im}\tau \to \infty$,
$$\Theta_Q\Big(\frac{a\tau+b}{c\tau+d}\Big)(c\tau+d)^{-k} \longrightarrow M_A(a, c)
  = \Big(\frac{-i}{2c}\Big)^k(\det A)^{-1/2}\,G_A(a, c)$$
(`thetaMult`; no level needed). *Proof:* the cusp expansion `thetaGram_cusp` and dominated convergence. -/
@[kb "iwaniec1997" "§10.3–10.4, theta at a cusp [unverified]"]
theorem tendsto_theta_cusp {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {a b d : ℤ} {c : ℕ}
    [NeZero c] (hdet : a * d - b * c = 1) :
    Tendsto (fun τ : UpperHalfPlane => theta Q ((a * τ + b) / (c * τ + d)) * (((c * τ + d : ℂ)) ^ k)⁻¹)
      UpperHalfPlane.atImInfty (𝓝 (thetaMult (gramMatrix Q) k a c)) := by
  have hA := gramMatrix_posDef hQ
  have hint := quadAt_gramMatrix_int Q
  have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne c)
  have hdet' : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  have hP : ((1 / 4 : ℝ) • (gramMatrix Q)⁻¹).PosDef := hA.inv.smul (by norm_num)
  set W : UpperHalfPlane → ℂ := fun τ => (c * τ + d) / c with hWdef
  have hWim : ∀ τ : UpperHalfPlane, (W τ).im = τ.im := by
    intro τ
    simp only [hWdef, add_div, mul_div_cancel_left₀ _ hc0]
    simp [Complex.div_im]
  have hfun : ∀ τ : UpperHalfPlane, theta Q ((a * τ + b) / (c * τ + d)) * (((c * τ + d : ℂ)) ^ k)⁻¹ =
      (-I / (2 * c)) ^ k * ((Real.sqrt (gramMatrix Q).det)⁻¹ : ℝ) *
        ∑' m : Fin n → ℤ, gaussSum (gramMatrix Q) a c m *
          cexp (2 * Real.pi * I * W τ * (quadAt ((1 / 4 : ℝ) • (gramMatrix Q)⁻¹) m : ℂ)) := by
    intro τ
    set w : ℂ := c * τ + d with hwdef
    have hw : 0 < w.im := by
      rw [hwdef]; simp only [add_im, mul_im, natCast_re, natCast_im, zero_mul, add_zero, intCast_im]
      exact mul_pos hcpos τ.im_pos
    have hw0 : w ≠ 0 := by rintro h; rw [h] at hw; simp at hw
    have hz' : (a * (τ : ℂ) + b) / (c * τ + d) = a / c - 1 / (c * w) := by
      rw [← hwdef]; field_simp; linear_combination (-1 : ℂ) * hdet'
    rw [hz', theta_eq_thetaGram, thetaGram_cusp hA hint a c hw,
      show ((n : ℂ) / 2) = ((k : ℕ) : ℂ) by rw [hn]; push_cast; ring, cpow_natCast]
    have : W τ = w / c := rfl
    rw [this, show -I * w / (2 * c) = (-I / (2 * c)) * w by ring, mul_pow]
    field_simp
  have hlim := tendsto_tsum_cexp_quad_filter hP (gaussSum (gramMatrix Q) a c)
    (norm_gaussSum_le _ a c) (W := W) (by simpa [hWim] using tendsto_im_atImInfty)
  have := (hlim.const_mul ((-I / (2 * c)) ^ k * ((Real.sqrt (gramMatrix Q).det)⁻¹ : ℝ)))
  rw [show thetaMult (gramMatrix Q) k a c = (-I / (2 * c)) ^ k * ((Real.sqrt (gramMatrix Q).det)⁻¹ : ℝ) *
      gaussSum (gramMatrix Q) a c 0 from rfl]
  exact this.congr fun τ => (hfun τ).symm

/-- The slash action of $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ on $\Theta_Q - \Theta_{Q'}$, written out. -/
lemma thetaH_sub_slash_apply (Q Q' : QuadForm ℤ n) (k : ℕ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ((thetaH Q - thetaH Q') ∣[(k : ℤ)] γ) τ =
      (theta Q (((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1)) -
        theta Q' (((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1))) *
        (((γ 1 0 : ℂ) * τ + γ 1 1) ^ k)⁻¹ := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, Pi.sub_apply]
  simp only [thetaH]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, eq_intCast, ofReal_intCast]
  rw [_root_.zpow_neg, zpow_natCast]

/-- **Vanishing at every cusp from equal cusp data.** For positive definite $Q$, $Q'$ in $n = 2k$ variables with
$M_A(a, c) = M_{A'}(a, c)$ for all $a$ and $c \ge 1$: $(\Theta_Q - \Theta_{Q'}) \mid_k \gamma \to 0$ at $i\infty$ for every
$\gamma \in \mathrm{SL}_2(\mathbb{Z})$. -/
theorem isZeroAtImInfty_slash_of_thetaMult_eq {Q Q' : IntQF n} (hQ : Q.PosDef) (hQ' : Q'.PosDef) {k : ℕ}
    (hn : n = 2 * k)
    (hM : ∀ (a : ℤ) (c : ℕ) [NeZero c], thetaMult (gramMatrix Q) k a c = thetaMult (gramMatrix Q') k a c)
    (γ : SL(2, ℤ)) : UpperHalfPlane.IsZeroAtImInfty ((thetaH Q - thetaH Q') ∣[(k : ℤ)] γ) := by
  unfold UpperHalfPlane.IsZeroAtImInfty ZeroAtFilter
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  simp_rw [funext (thetaH_sub_slash_apply Q Q' k γ)]
  generalize γ 0 0 = a, γ 0 1 = b, γ 1 0 = c, γ 1 1 = d at hdet ⊢
  rcases lt_trichotomy c 0 with hc | hc | hc
  · -- `c < 0`: use `-γ`
    set c' : ℕ := (-c).toNat with hc'
    have hc'c : (c' : ℤ) = -c := by rw [hc']; omega
    have : NeZero c' := ⟨by omega⟩
    have hdet' : (-a) * (-d) - (-b) * (c' : ℤ) = 1 := by rw [hc'c]; linarith
    have h1 := tendsto_theta_cusp hQ hn hdet'
    have h2 := tendsto_theta_cusp hQ' hn hdet'
    have hlim := ((h1.sub h2).const_mul ((-1 : ℂ) ^ k))
    rw [hM, sub_self, mul_zero] at hlim
    refine hlim.congr fun τ => ?_
    have e : (c' : ℂ) = -(c : ℂ) := by exact_mod_cast hc'c
    rw [e]
    push_cast
    rw [show -(a : ℂ) * τ + -b = -(a * τ + b) by ring, show -(c : ℂ) * τ + -d = -(c * τ + d) by ring,
      neg_div_neg_eq, neg_eq_neg_one_mul (c * (τ : ℂ) + d), mul_pow, mul_inv]
    have : ((-1 : ℂ) ^ k)⁻¹ = (-1) ^ k := by rw [← inv_pow, inv_neg, inv_one]
    rw [this]; ring_nf
    rw [show ((-1 : ℂ)) ^ (k * 2) = 1 by rw [pow_mul']; simp]; ring
  · -- `c = 0`: `γ = ±T^b`
    subst hc
    have had : a * d = 1 := by linarith
    have hd : d = 1 ∨ d = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    have ha : a = d := by rcases hd with rfl | rfl <;> omega
    subst ha
    have hτ' : ∀ τ : UpperHalfPlane, ((a : ℂ) * τ + b) / (((0 : ℤ) : ℂ) * τ + a) = τ + (a * b : ℤ) := by
      intro τ; rcases hd with rfl | rfl <;> push_cast <;> field_simp <;> ring
    have hlim := ((tendsto_theta_atImInfty hQ).sub (tendsto_theta_atImInfty hQ')).mul_const
      ((((0 : ℤ) : ℂ) * (0 : ℂ) + a) ^ k)⁻¹
    rw [sub_self, zero_mul] at hlim
    refine hlim.congr fun τ => ?_
    rw [hτ', theta_add_int, theta_add_int]
    simp
  · set c' : ℕ := c.toNat with hc'
    have hc'c : (c' : ℤ) = c := by rw [hc']; omega
    have : NeZero c' := ⟨by omega⟩
    have hdet' : a * d - b * (c' : ℤ) = 1 := by rw [hc'c]; exact hdet
    have h1 := tendsto_theta_cusp hQ hn hdet'
    have h2 := tendsto_theta_cusp hQ' hn hdet'
    have hlim := h1.sub h2
    rw [hM, sub_self] at hlim
    have e : (c' : ℂ) = (c : ℂ) := by exact_mod_cast hc'c
    rw [e] at hlim
    refine hlim.congr fun τ => ?_
    ring

/-- **$\Theta_Q - \Theta_{Q'}$ vanishes at every cusp for $Q'$ in the genus of $Q$** ($Q$ positive definite, $n = 2k$):
for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, $(\Theta_Q - \Theta_{Q'}) \mid_k \gamma \to 0$ as $\operatorname{Im}\tau \to \infty$,
i.e. the constant terms of $\Theta_Q$ and $\Theta_{Q'}$ agree at every cusp (`SameGenus.thetaMult_eq`). -/
@[kb "iwaniec1997" "§10.4; Hanke 2004 (4.3)–(4.5), p. 365 [unverified]"]
theorem isZeroAtImInfty_theta_sub_slash {Q Q' : IntQF n} (hQ : Q.PosDef) (h : SameGenus Q Q') {k : ℕ}
    (hn : n = 2 * k) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty ((thetaH Q - thetaH Q') ∣[(k : ℤ)] γ) :=
  isZeroAtImInfty_slash_of_thetaMult_eq hQ (h.posDef hQ) hn
    (fun a c _ => h.thetaMult_eq hQ k a c) γ

/-! ### $\Theta_Q - \Theta_{Q'} \in S_k(\Gamma_1(N))$ -/

/-- **$\Theta_Q - \Theta_{Q'}$ is a cusp form of weight $k$ for $\Gamma_1(N)$** ($Q$ positive definite in $n = 2k$
variables, $Q'$ in its genus, $N \ge 1$ a level of both): Mathlib's `CuspForm Γ₁(N) k`, from `thetaMFGamma1` and
`isZeroAtImInfty_theta_sub_slash`. With `thetaH_sub_slash_gamma0` this is
$\Theta_Q - \Theta_{Q'} \in S_k(\Gamma_0(N), \chi_Q)$. -/
@[kb "hanke2004" "(4.3), p. 365 (Θ_Q − Θ_{Q'} cuspidal) [unverified]"]
def thetaCuspDiff {Q Q' : IntQF n} (hQ : Q.PosDef) (h : SameGenus Q Q') {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) (hN' : IsThetaLevel Q' N) :
    CuspForm (CongruenceSubgroup.Gamma1 N) k where
  toSlashInvariantForm :=
    (thetaMFGamma1 hQ hn hN0 hN - thetaMFGamma1 (h.posDef hQ) hn hN0 hN').toSlashInvariantForm
  holo' := (thetaMFGamma1 hQ hn hN0 hN - thetaMFGamma1 (h.posDef hQ) hn hN0 hN').holo'
  zero_at_cusps' hc := by
    have : NeZero N := ⟨hN0.ne'⟩
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    exact fun γ _ => isZeroAtImInfty_theta_sub_slash hQ h hn γ

@[simp] theorem thetaCuspDiff_apply {Q Q' : IntQF n} (hQ : Q.PosDef) (h : SameGenus Q Q') {k : ℕ}
    (hn : n = 2 * k) {N : ℕ} (hN0 : 0 < N) (hN : IsThetaLevel Q N) (hN' : IsThetaLevel Q' N)
    (τ : UpperHalfPlane) : thetaCuspDiff hQ h hn hN0 hN hN' τ = theta Q τ - theta Q' τ := rfl

/-- $\chi_{Q'} = \chi_Q$ for $Q'$ in the genus of $Q$ (`thetaChi` depends only on $\det H$). -/
theorem SameGenus.thetaChi_eq {Q Q' : IntQF n} (hQ : Q.PosDef) (h : SameGenus Q Q') (k N : ℕ) (d : ℤ) :
    thetaChi Q k N d = thetaChi Q' k N d := by
  simp only [thetaChi, thetaDisc, h.det_hessian_eq hQ]

/-- **The character of $\Theta_Q - \Theta_{Q'}$ on $\Gamma_0(N)$:** $(\Theta_Q - \Theta_{Q'}) \mid_k \gamma =
\chi_Q(d)\,(\Theta_Q - \Theta_{Q'})$ for $\gamma \in \Gamma_0(N)$, $d = \gamma_{11}$ (0-based entries). -/
@[kb "hanke2004" "§4, p. 364 [unverified]"]
theorem thetaH_sub_slash_gamma0 {Q Q' : IntQF n} (hQ : Q.PosDef) (h : SameGenus Q Q') {k : ℕ}
    (hn : n = 2 * k) {N : ℕ} (hN0 : 0 < N) (hN : IsThetaLevel Q N) (hN' : IsThetaLevel Q' N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (thetaH Q - thetaH Q') ∣[(k : ℤ)] γ = (thetaChi Q k N (γ 1 1) : ℂ) • (thetaH Q - thetaH Q') := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, thetaH_slash_gamma0 hQ hn hN0 hN hγ,
    thetaH_slash_gamma0 (h.posDef hQ) hn hN0 hN' hγ, ← h.thetaChi_eq hQ, smul_add, smul_neg]

/-! ### The genus theta series -/

/-- For $c \in \mathrm{Gen}(Q)$, the chosen representative `c.out` lies in the genus of $Q$. -/
theorem sameGenus_out_of_mem {Q : QuadForm ℤ n} {c : QClass n} (hc : c ∈ genusClasses Q) :
    SameGenus Q c.out := by
  obtain ⟨Q', hQ', hg⟩ := hc
  have : IntEquiv Q' c.out := by
    rw [← classOf_eq_classOf_iff, hQ']; exact (Quotient.out_eq c).symm
  exact hg.trans this.sameGenus

theorem QClass.repNum_eq_out (c : QClass n) (m : ℤ) :
    c.repNum m = _root_.QuadFormsKB.Siegel.repNum c.out m := by
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

theorem QClass.autCard_eq_out (c : QClass n) : c.autCard = Nat.card (Aut c.out) := by
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

/-- **The genus theta series** (Hanke 2004, (4.5), p. 366; Siegel):
$$\Theta_{\mathrm{Gen}(Q)}(z) = \frac{1}{\mathrm{Mass}(Q)}\sum_{[Q'] \in \mathrm{Gen}(Q)}\frac{\Theta_{Q'}(z)}{|\mathrm{Aut}(Q')|},$$
over $\mathrm{GL}_n(\mathbb{Z})$-classes (one representative `c.out` per class; $\Theta$ is a class invariant). A
`finsum`, meaningful under `GenusFinite`. Its $q$-expansion is $\sum_m a_E(m)e(mz)$ (`hasSum_thetaGen`). -/
@[kb "hanke2004" "(4.5), p. 366 [unverified]"]
def thetaGen (Q : QuadForm ℤ n) (z : ℂ) : ℂ :=
  (((mass Q)⁻¹ : ℝ) : ℂ) * ∑ᶠ c ∈ genusClasses Q, (((c.autCard : ℝ))⁻¹ : ℂ) * theta c.out z

theorem thetaGen_eq_sum {Q : QuadForm ℤ n} (hF : GenusFinite Q) (z : ℂ) :
    thetaGen Q z = (((mass Q)⁻¹ : ℝ) : ℂ) *
      ∑ c ∈ hF.finite_classes.toFinset, (((c.autCard : ℝ))⁻¹ : ℂ) * theta c.out z := by
  rw [thetaGen, finsum_mem_eq_finite_toFinset_sum _ hF.finite_classes]

/-- **The $q$-expansion of the genus theta series:** $\Theta_{\mathrm{Gen}(Q)}(z) = \sum_{m \ge 0}a_E(m)e(mz)$ with
$a_E(m)$ = `genusRepAvg` ($a_E(0) = 1$), for $Q$ positive definite, `GenusFinite`, $\operatorname{Im} z > 0$. -/
@[kb "hanke2004" "(4.5), p. 366 [unverified]"]
theorem hasSum_thetaGen {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun m : ℕ => (genusRepAvg Q m : ℂ) * cexp (2 * Real.pi * I * z * m)) (thetaGen Q z) := by
  rw [thetaGen_eq_sum hF]
  set s := hF.finite_classes.toFinset
  have h := (hasSum_sum (s := s) (fun c hc =>
    ((hasSum_theta ((sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp hc)).posDef hQ) hz).mul_left
      (((c.autCard : ℝ))⁻¹ : ℂ)))).mul_left (((mass Q)⁻¹ : ℝ) : ℂ)
  refine h.congr_fun fun m => ?_
  rw [genusRepAvg, genusRepSum, finsum_mem_eq_finite_toFinset_sum _ hF.finite_classes]
  push_cast
  rw [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [QClass.repNum_eq_out]
  ring

/-- $\sum_{[Q'] \in \mathrm{Gen}(Q)}|\mathrm{Aut}(Q')|^{-1} = \mathrm{Mass}(Q)$. -/
lemma sum_autCard_inv {Q : QuadForm ℤ n} (hF : GenusFinite Q) :
    ∑ c ∈ hF.finite_classes.toFinset, (((c.autCard : ℝ))⁻¹ : ℂ) = ((mass Q : ℝ) : ℂ) := by
  rw [mass_eq_sum hF]; push_cast; rfl

/-- **A common level for the genus:** under `GenusFinite`, some $N \ge 1$ is a level (`IsThetaLevel`) of every form in
the genus of $Q$ (the product of the levels of class representatives; levels are class invariants,
`level_eq_of_intEquiv`). -/
theorem exists_isThetaLevel_genus {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) :
    ∃ N, 0 < N ∧ ∀ Q', SameGenus Q Q' → IsThetaLevel Q' N := by
  classical
  set s := hF.finite_classes.toFinset
  refine ⟨∏ c ∈ s, level c.out, Finset.prod_pos fun c hc => level_pos (IntQF.PosDef.nondegenerate
    ((sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp hc)).posDef hQ)), fun Q' hQ' => ?_⟩
  have hnd := IntQF.PosDef.nondegenerate (hQ'.posDef hQ)
  have hc : classOf Q' ∈ s := (Set.Finite.mem_toFinset _).mpr (classOf_mem_genusClasses_iff.mpr hQ')
  have he : IntEquiv (classOf Q').out Q' := by
    rw [← classOf_eq_classOf_iff]; exact Quotient.out_eq _
  rw [← isLevel_iff_isThetaLevel hnd, isLevel_iff_level_dvd hnd, ← level_eq_of_intEquiv he]
  exact Finset.dvd_prod_of_mem _ hc

/-- **$\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ is a cusp form of weight $k$ for $\Gamma_1(N)$** (Hanke 2004, (4.3)–(4.5);
$Q$ positive definite in $n = 2k$ variables, `GenusFinite`, $N \ge 1$ a level of every form in the genus, e.g. from
`exists_isThetaLevel_genus`): the combination
$\mathrm{Mass}(Q)^{-1}\sum_{[Q']}|\mathrm{Aut}(Q')|^{-1}(\Theta_Q - \Theta_{Q'})$ of the cusp forms `thetaCuspDiff`
(`thetaGenCusp_apply`). It transforms with $\chi_Q$ under $\Gamma_0(N)$ (`thetaGenCusp_slash_gamma0`). -/
@[kb "hanke2004" "(4.3)–(4.5), pp. 365–366 [unverified]"]
def thetaGenCusp {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : ∀ Q', SameGenus Q Q' → IsThetaLevel Q' N) :
    CuspForm (CongruenceSubgroup.Gamma1 N) k :=
  (mass Q)⁻¹ • ∑ c ∈ hF.finite_classes.toFinset.attach, ((c.1.autCard : ℝ))⁻¹ •
    thetaCuspDiff hQ (sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp c.2)) hn hN0
      (hN Q (SameGenus.refl Q)) (hN _ (sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp c.2)))

lemma cuspForm_sum_apply {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (f : ι → CuspForm Γ k) (τ : UpperHalfPlane) : (∑ i ∈ s, f i) τ = ∑ i ∈ s, f i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- **$\texttt{thetaGenCusp} = \Theta_Q - \Theta_{\mathrm{Gen}(Q)}$** on the upper half plane. -/
theorem thetaGenCusp_apply {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) {k : ℕ} (hn : n = 2 * k)
    {N : ℕ} (hN0 : 0 < N) (hN : ∀ Q', SameGenus Q Q' → IsThetaLevel Q' N) (τ : UpperHalfPlane) :
    thetaGenCusp hQ hF hn hN0 hN τ = theta Q τ - thetaGen Q τ := by
  have hm := mass_pos hQ hF
  have hm0 : ((mass Q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [thetaGenCusp, thetaGen_eq_sum hF]
  simp only [IsSMulApply.smul_apply, cuspForm_sum_apply, thetaCuspDiff_apply, real_smul]
  push_cast
  rw [Finset.sum_attach hF.finite_classes.toFinset
    (fun c => ((c.autCard : ℂ))⁻¹ * (theta Q τ - theta c.out τ))]
  have hs : ∑ c ∈ hF.finite_classes.toFinset, ((c.autCard : ℂ))⁻¹ = (mass Q : ℂ) := by
    have := sum_autCard_inv hF; push_cast at this; exact this
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
  field_simp

/-- $\Theta_Q - \Theta_{\mathrm{Gen}(Q)} = \mathrm{Mass}(Q)^{-1}\sum_{[Q']}|\mathrm{Aut}(Q')|^{-1}(\Theta_Q - \Theta_{Q'})$. -/
lemma theta_sub_thetaGen {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) (z : ℂ) :
    theta Q z - thetaGen Q z = ((mass Q : ℂ))⁻¹ *
      ∑ c ∈ hF.finite_classes.toFinset, ((c.autCard : ℂ))⁻¹ * (theta Q z - theta c.out z) := by
  have hm0 : ((mass Q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mass_pos hQ hF).ne'
  have hs : ∑ c ∈ hF.finite_classes.toFinset, ((c.autCard : ℂ))⁻¹ = (mass Q : ℂ) := by
    have := sum_autCard_inv hF; push_cast at this; exact this
  rw [thetaGen_eq_sum hF]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
  field_simp

/-- **The character of $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ on $\Gamma_0(N)$:** $(\Theta_Q - \Theta_{\mathrm{Gen}(Q)}) \mid_k \gamma
= \chi_Q(d)\,(\Theta_Q - \Theta_{\mathrm{Gen}(Q)})$ for $\gamma \in \Gamma_0(N)$, $d = \gamma_{11}$; so `thetaGenCusp`
$\in S_k(\Gamma_0(N), \chi_Q)$. -/
@[kb "hanke2004" "§4, p. 364; (4.3), p. 365 [unverified]"]
theorem thetaGenCusp_slash_gamma0 {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) {k : ℕ}
    (hn : n = 2 * k) {N : ℕ} (hN0 : 0 < N) (hN : ∀ Q', SameGenus Q Q' → IsThetaLevel Q' N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ⇑(thetaGenCusp hQ hF hn hN0 hN) ∣[(k : ℤ)] γ =
      (thetaChi Q k N (γ 1 1) : ℂ) • ⇑(thetaGenCusp hQ hF hn hN0 hN) := by
  ext τ
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul, thetaGenCusp_apply, thetaGenCusp_apply,
    theta_sub_thetaGen hQ hF, theta_sub_thetaGen hQ hF, mul_assoc, Finset.sum_mul, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  have h := congrFun (thetaH_sub_slash_gamma0 hQ (sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp hc))
    hn hN0 (hN Q (SameGenus.refl Q)) (hN _ (sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp hc))) hγ) τ
  rw [ModularForm.SL_slash_apply] at h
  simp only [Pi.sub_apply, Pi.smul_apply, thetaH, smul_eq_mul] at h
  rw [mul_assoc (((c.autCard : ℂ))⁻¹), h]; ring

end

end QuadFormsKB.Siegel
