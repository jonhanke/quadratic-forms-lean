/-
# The proper classes of an indefinite genus as an idèle class group (Shimura 1999, Lemma 2.4(4))

**Layer:** number fields; the spinor norm $\sigma$ (`Lattices/SpinorNorm.lean`), the adelic group $SO(V)(\mathbb A_f)$
(`SOAf`), its subgroup $\Gamma_fK = SO(V)(F)\,SO(\hat L)$ (`classSub`, `Hanke2005/ClassIndex.lean`), Mathlib's idèle group
$F^\times_{\mathbb A}$ = `IdeleGroup (𝓞 F) F` with its principal idèles $F^\times$ (`IdeleGroup.principalSubgroup`), the idèle
components `OMeara.ideleAt`, `OMeara.ideleAtInf` (`OMeara/Sec64.lean`) and O'Meara 101:8 (`OMeara/Sec101BD.lean`).

Shimura (1999, §2, pp. 7–8): $G = SO(V)$, $D = G_{\mathbf a}\times\prod_{v\in\mathbf h}D_v$ the stabilizer of a lattice $L$
(here $L = \mathcal O_F^n$, $D_v = SO(L_v)$), and for a subgroup $H$ of $G_{\mathbb A}$, $\sigma(H)$ is the subgroup of
$F^\times_{\mathbb A}$ containing $F^{\times2}_{\mathbb A}$ with $\sigma(H)/F^{\times2}_{\mathbb A}$ the image of $H$ under the spinor norm
$G_{\mathbb A}\to F^\times_{\mathbb A}/F^{\times2}_{\mathbb A}$ (2.1.1). **Lemma 2.4(4)**: for $n\ge3$ and $G_{\mathbf a}$ not compact, the map
$x\mapsto\sigma(x)$ defines a bijection of $G\backslash G_{\mathbb A}/D$ onto $F^\times_{\mathbb A}/F^\times\sigma(D)$.

**Defines**
* `sigmaInf Q hQ w` $=\sigma(G_w)\subseteq F_w^\times/F_w^{\times2}$ and `sigmaFin Q hQ v` $=\sigma(D_v) = \sigma(SO(L_v))$;
* `sigmaD Q hQ` $=\sigma(D)$: the idèles $x$ with $x_w\in\sigma(G_w)$ at every infinite place and $x_v\in\sigma(D_v)$ at
  every finite place (modulo squares). Since $D$ is the product of its local components and
  $F^\times_{\mathbb A}/F^{\times2}_{\mathbb A}\to\prod_vF_v^\times/F_v^{\times2}$ is injective, this is Shimura's $\sigma(D)$;
* `classIdeleSub Q hQ` $= F^\times\sigma(D)$;
* `SpinorRel Q hQ b x` ("$x$ represents $\sigma(b)$ modulo $\sigma(D)$") and **`spinorIdeleHom`**, the homomorphism
  $SO(V)(\mathbb A_f)\to F^\times_{\mathbb A}/F^\times\sigma(D)$, $b\mapsto\sigma(b)$ (`spinorIdeleHom_eq`).

**Proves** (for $L = \mathcal O_F^n$, $Q_0$ nondegenerate and indefinite, $n\ge3$)
* `ker_spinorIdeleHom`: $\ker = \Gamma_fK$; the inclusion $\supseteq$ is $\sigma(\gamma)\in F^\times$, $\sigma(k)\in\sigma(D)$;
  $\subseteq$ is Shimura's proof: $\sigma(b)\equiv a$ with $a\in F^\times$ and $a_w\in\sigma(G_w)$ for all infinite $w$, so
  $a = \sigma(\alpha)$, $\alpha\in G$ (his Lemma 2.2(3); here O'Meara 101:8, `exists_evalIn_eq_mul_of_isSquare`), and
  $\alpha^{-1}b\in O'(V_{\mathbb A_f})\,SO(\hat L)\subseteq\Gamma_fK$ (strong approximation, `spinorKernel_le_classSub`);
* `spinorIdeleHom_surjective`: Shimura's $\sigma(G_{\mathbb A}) = W$ and $F^\times W = F^\times_{\mathbb A}$: weak approximation at
  the infinite places (Mathlib's `InfiniteAdeleRing.denseRange_algebraMap`) moves the archimedean components into
  $F_w^{\times2}$, and the local surjectivity $\sigma(SO(V_v)) = F_v^\times$ (`exists_so_spinorNorm_local`) handles the finite
  places; $\sigma(SO(L_v))\supseteq\mathfrak o_v^\times$ at the places $v\nmid2\det H$ (`unit_mem_sigmaFin`);
* **`shimuraLemma24_4`**: $SO(V)(\mathbb A_f)/\Gamma_fK\simeq F^\times_{\mathbb A}/F^\times\sigma(D)$ (a group isomorphism induced
  by the spinor norm), and **`dcEquivIdele`**: $SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)\simeq F^\times_{\mathbb A}/F^\times\sigma(D)$,
  with `dcEquivIdele_mk`: the class of $b$ goes to the class of any idèle representing $\sigma(b)$;
* `card_DC_eq_index_idele`: the number of proper classes is $[F^\times_{\mathbb A}:F^\times\sigma(D)]$.

The double cosets here are $G\backslash G_{\mathbf h}/D_{\mathbf h}$; they are Shimura's $G\backslash G_{\mathbb A}/D$ because $D\supseteq G_{\mathbf a}$.
All unconditional, standard axioms only.
-/
import QuadFormsKB.Literature.Hanke2005.ClassIndex
import QuadFormsKB.Literature.Hanke2005.SpinorSurjLocal
import QuadFormsKB.Literature.OMeara.Sec101BD
import QuadFormsKB.Lattices.SAVecAux

open NumberField IsDedekindDomain Matrix
open QuadFormsKB.OMeara (ideleAt ideleAtInf ideleAt_mul ideleAt_one ideleAt_inv ideleAtInf_mul ideleAtInf_one
  ideleAtInf_inv ideleAt_ofAdic_self ideleAt_ofAdic_ne ideleAtInf_ofAdic)

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005.SpinorIdele

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005.EqualMasses

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "J" => IdeleGroup (𝓞 F) F

theorem charZero_completion (w : InfinitePlace F) : CharZero w.Completion :=
  charZero_of_injective_algebraMap (algebraMap F _).injective

attribute [local instance] charZero_completion

/-! ### Square classes -/

section SqClass

variable {K : Type*} [Field K] [CharZero K]

theorem sqClassOf_inv (a : K) : sqClassOf a⁻¹ = sqClassOf a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h := sqClassOf_mul (inv_ne_zero ha) (mul_ne_zero ha ha)
  rw [show a⁻¹ * (a * a) = a by field_simp, (sqClassOf_eq_one_iff (mul_ne_zero ha ha)).mpr ⟨a, rfl⟩,
    mul_one] at h
  exact h.symm

theorem isSquare_of_sqClassOf_eq_one {a : K} (ha : a ≠ 0) (h : sqClassOf a = 1) : IsSquare a :=
  (sqClassOf_eq_one_iff ha).mp h

end SqClass

/-! ### Idèle components -/

theorem ideleAt_ne_zero (x : J) (v : HeightOneSpectrum (𝓞 F)) : ideleAt x v ≠ 0 := by
  intro h
  have := ideleAt_mul x x⁻¹ v
  rw [mul_inv_cancel, ideleAt_one, h, zero_mul] at this
  exact one_ne_zero this

theorem ideleAtInf_ne_zero (x : J) (w : InfinitePlace F) : ideleAtInf x w ≠ 0 := by
  intro h
  have := ideleAtInf_mul x x⁻¹ w
  rw [mul_inv_cancel, ideleAtInf_one, h, zero_mul] at this
  exact one_ne_zero this

/-- The component at a finite place, as a monoid homomorphism. -/
def ideleAtHom (v : HeightOneSpectrum (𝓞 F)) : J →* v.adicCompletion F where
  toFun x := ideleAt x v
  map_one' := ideleAt_one v
  map_mul' x y := ideleAt_mul x y v

theorem ideleAt_unitEmbedding (a : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F a) v = algebraMap F (v.adicCompletion F) a := rfl

theorem ideleAtInf_unitEmbedding (a : Fˣ) (w : InfinitePlace F) :
    ideleAtInf (IdeleGroup.unitEmbedding (𝓞 F) F a) w = algebraMap F w.Completion a := rfl

/-! ### The local spinor-norm groups $\sigma(G_w)$, $\sigma(D_v)$ and $\sigma(D)$ -/

section Sigma

variable (Q : QuadForm F n) (hQ : Q.Nondegenerate)

/-- **$\sigma(G_w)$** (Shimura 1999, (2.1.1) and Lemma 2.2(1)): the spinor norms of $SO(V)(F_w)$ at an infinite place $w$,
as a subgroup of $F_w^\times/F_w^{\times2}$. -/
@[kb "shimura1999" "§2.1, p. 7 (σ(G_v), v ∈ a)"]
def sigmaInf (w : InfinitePlace F) : Subgroup (SqClass w.Completion) :=
  (soSub Q w.Completion).map (spinorNormHom Q w.Completion hQ)

/-- **$\sigma(D_v) = \sigma(SO(L_v))$** at a finite place $v$, $L_v = \mathfrak o_v^n$: the spinor norms of the rotations
preserving $\mathfrak o_v^n$, as a subgroup of $F_v^\times/F_v^{\times2}$. -/
@[kb "shimura1999" "§2.1, p. 7 and Lemma 2.4, p. 8 (σ(D_v), D_v the stabilizer of L_v)"]
def sigmaFin (v : HeightOneSpectrum (𝓞 F)) : Subgroup (SqClass (v.adicCompletion F)) :=
  (stdStab Q v ⊓ soSub Q (v.adicCompletion F)).map (spinorNormHom Q (v.adicCompletion F) hQ)

theorem mem_sigmaInf {w : InfinitePlace F} {c : SqClass w.Completion} :
    c ∈ sigmaInf Q hQ w ↔ ∃ g ∈ soSub Q w.Completion, spinorNorm Q w.Completion g = c := by
  simp [sigmaInf, spinorNormHom_apply]

theorem mem_sigmaFin {v : HeightOneSpectrum (𝓞 F)} {c : SqClass (v.adicCompletion F)} :
    c ∈ sigmaFin Q hQ v ↔
      ∃ g ∈ stdStab Q v ⊓ soSub Q (v.adicCompletion F), spinorNorm Q (v.adicCompletion F) g = c := by
  simp [sigmaFin, spinorNormHom_apply]

/-- **$\sigma(D)$** (Shimura 1999, §2.1, p. 7), $D = \prod_{w\in\mathbf a}G_w\times\prod_{v\in\mathbf h}SO(L_v)$: the idèles $x$ with
$x_wF_w^{\times2}\in\sigma(G_w)$ for every infinite place $w$ and $x_vF_v^{\times2}\in\sigma(SO(L_v))$ for every finite place $v$.
(It contains $F^{\times2}_{\mathbb A}$.) -/
@[kb "shimura1999" "§2.1, p. 7 (σ(D) ⊆ F_A^×, containing F_A^{×2})"]
def sigmaD : Subgroup J where
  carrier := {x | (∀ w, sqClassOf (ideleAtInf x w) ∈ sigmaInf Q hQ w) ∧
    ∀ v, sqClassOf (ideleAt x v) ∈ sigmaFin Q hQ v}
  one_mem' := ⟨fun w => by rw [ideleAtInf_one, sqClassOf_one]; exact Subgroup.one_mem _,
    fun v => by rw [ideleAt_one, sqClassOf_one]; exact Subgroup.one_mem _⟩
  mul_mem' {x y} hx hy := ⟨fun w => by
      rw [ideleAtInf_mul, sqClassOf_mul (ideleAtInf_ne_zero x w) (ideleAtInf_ne_zero y w)]
      exact Subgroup.mul_mem _ (hx.1 w) (hy.1 w),
    fun v => by
      rw [ideleAt_mul, sqClassOf_mul (ideleAt_ne_zero x v) (ideleAt_ne_zero y v)]
      exact Subgroup.mul_mem _ (hx.2 v) (hy.2 v)⟩
  inv_mem' {x} hx := ⟨fun w => by rw [ideleAtInf_inv, sqClassOf_inv]; exact hx.1 w,
    fun v => by rw [ideleAt_inv, sqClassOf_inv]; exact hx.2 v⟩

/-- **$F^\times\sigma(D)$**, the subgroup of $F^\times_{\mathbb A}$ generated by the principal idèles and $\sigma(D)$ (Shimura 1999,
Lemma 2.4(4)). -/
@[kb "shimura1999" "Lemma 2.4(4), p. 8 (F^×σ(D))"]
def classIdeleSub : Subgroup J := IdeleGroup.principalSubgroup (𝓞 F) F ⊔ sigmaD Q hQ

/-- **$x$ represents $\sigma(b)$ modulo $\sigma(D)$**, for $b\in SO(V)(\mathbb A_f)$ (archimedean components $1$) and an idèle $x$:
$x_w\in\sigma(G_w)$ at every infinite place, and $x_v\,\sigma(b_v)\in\sigma(SO(L_v))$ at every finite place. -/
def SpinorRel (b : soAf Q) (x : J) : Prop :=
  (∀ w, sqClassOf (ideleAtInf x w) ∈ sigmaInf Q hQ w) ∧
    ∀ v, sqClassOf (ideleAt x v) * spinorNorm Q (v.adicCompletion F) ((b : OAf Q) v) ∈ sigmaFin Q hQ v

theorem spinorNorm_one' (hQ : Q.Nondegenerate) (K : Type*) [Field K] [Algebra F K] [CharZero K] :
    spinorNorm Q K 1 = 1 := by
  rw [← spinorNormHom_apply Q K hQ, map_one]

theorem spinorRel_one_iff (x : J) : SpinorRel Q hQ 1 x ↔ x ∈ sigmaD Q hQ := by
  unfold SpinorRel
  simp only [OneMemClass.coe_one]
  change _ ↔ (_ ∧ _)
  refine and_congr Iff.rfl (forall_congr' fun v => ?_)
  rw [show ((1 : OAf Q) v) = 1 from rfl, spinorNorm_one' Q hQ, mul_one]

theorem spinorRel_mul {b b' : soAf Q} {x y : J} (h : SpinorRel Q hQ b x) (h' : SpinorRel Q hQ b' y) :
    SpinorRel Q hQ (b * b') (x * y) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · rw [ideleAtInf_mul, sqClassOf_mul (ideleAtInf_ne_zero x w) (ideleAtInf_ne_zero y w)]
    exact Subgroup.mul_mem _ (h.1 w) (h'.1 w)
  · have e : ((b * b' : soAf Q) : OAf Q) v = (b : OAf Q) v * (b' : OAf Q) v := rfl
    rw [ideleAt_mul, sqClassOf_mul (ideleAt_ne_zero x v) (ideleAt_ne_zero y v), e,
      ← spinorNormHom_apply Q _ hQ, map_mul, spinorNormHom_apply, spinorNormHom_apply]
    have := Subgroup.mul_mem _ (h.2 v) (h'.2 v)
    convert this using 1
    ac_rfl

theorem inv_mul_mem_sigmaD_of_spinorRel {b : soAf Q} {x y : J} (h : SpinorRel Q hQ b x)
    (h' : SpinorRel Q hQ b y) : x⁻¹ * y ∈ sigmaD Q hQ := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · rw [ideleAtInf_mul, ideleAtInf_inv, sqClassOf_mul (inv_ne_zero (ideleAtInf_ne_zero x w))
      (ideleAtInf_ne_zero y w), sqClassOf_inv]
    exact Subgroup.mul_mem _ (h.1 w) (h'.1 w)
  · rw [ideleAt_mul, ideleAt_inv, sqClassOf_mul (inv_ne_zero (ideleAt_ne_zero x v))
      (ideleAt_ne_zero y v), sqClassOf_inv]
    have := Subgroup.mul_mem _ (h.2 v) (h'.2 v)
    convert this using 1
    set s := spinorNorm Q (v.adicCompletion F) ((b : OAf Q) v)
    calc sqClassOf (ideleAt x v) * sqClassOf (ideleAt y v)
        = sqClassOf (ideleAt x v) * sqClassOf (ideleAt y v) * (s * s) := by rw [SqClass.mul_self, mul_one]
      _ = _ := by ac_rfl

/-- **Every $\sigma(b)$ is represented by an idèle**: for $b\in SO(V)(\mathbb A_f)$ choose $c_v$ with $c_vF_v^{\times2} = \sigma(b_v)$
at the finitely many $v$ with $b_v\notin SO(L_v)$, and $1$ elsewhere. -/
theorem exists_spinorRel (b : soAf Q) : ∃ x : J, SpinorRel Q hQ b x := by
  classical
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : v.adicCompletion F, c ≠ 0 ∧
      spinorNorm Q (v.adicCompletion F) ((b : OAf Q) v) = sqClassOf c := by
    intro v
    obtain ⟨xs, hxs, hxe⟩ := exists_symmProd_eq Q (v.adicCompletion F) hQ ((b : OAf Q) v)
    exact ⟨_, valProd_ne_zero Q _ hxs, by rw [← hxe, spinorNorm_symmProd Q _ hQ xs hxs]⟩
  choose c hc0 hcσ using hc
  have hfin : {v | (b : OAf Q) v ∉ stdStab Q v}.Finite := Filter.eventually_cofinite.mp (b : OAf Q).2
  set S := hfin.toFinset
  let x : J := ∏ v ∈ S, IdeleGroup.ofAdicCompletion (𝓞 F) F v (Units.mk0 (c v) (hc0 v))
  have hxv : ∀ v, ideleAt x v = if v ∈ S then c v else 1 := by
    intro v
    change ideleAtHom v x = _
    simp only [x, map_prod]
    split_ifs with hv
    · rw [Finset.prod_eq_single_of_mem v hv]
      · exact ideleAt_ofAdic_self v _
      · intro v' _ hv'
        exact ideleAt_ofAdic_ne v' v (Ne.symm hv') _
    · refine Finset.prod_eq_one fun v' hv' => ?_
      exact ideleAt_ofAdic_ne v' v (fun h => hv (h ▸ hv')) _
  have hxw : ∀ w, ideleAtInf x w = 1 := by
    intro w
    simp only [x]
    induction S using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, ideleAtInf_mul, ideleAtInf_ofAdic, ih, one_mul]
  refine ⟨x, fun w => ?_, fun v => ?_⟩
  · rw [hxw, sqClassOf_one]; exact Subgroup.one_mem _
  · rw [hxv]
    split_ifs with hv
    · rw [hcσ, SqClass.mul_self]; exact Subgroup.one_mem _
    · rw [sqClassOf_one, one_mul, mem_sigmaFin]
      refine ⟨(b : OAf Q) v, ⟨?_, b.2 v⟩, rfl⟩
      by_contra hc'
      exact hv (hfin.mem_toFinset.mpr hc')

/-- **The spinor norm on $SO(V)(\mathbb A_f)$ with values in $F^\times_{\mathbb A}/F^\times\sigma(D)$** (Shimura 1999, (2.1.1) and
Lemma 2.4(4): "the map $x\mapsto\sigma(x)$"): $b\mapsto$ the class of any idèle representing $\sigma(b)$ (`spinorIdeleHom_eq`). -/
@[kb "shimura1999" "(2.1.1), p. 7 and Lemma 2.4(4), p. 8 (the map x ↦ σ(x))"]
def spinorIdeleHom : soAf Q →* J ⧸ classIdeleSub Q hQ where
  toFun b := QuotientGroup.mk (exists_spinorRel Q hQ b).choose
  map_one' := by
    rw [← QuotientGroup.mk_one, QuotientGroup.eq]
    refine Subgroup.mem_sup_right ?_
    have := (exists_spinorRel Q hQ 1).choose_spec
    rw [spinorRel_one_iff] at this
    simpa using this
  map_mul' b b' := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact Subgroup.mem_sup_right (inv_mul_mem_sigmaD_of_spinorRel Q hQ
      (exists_spinorRel Q hQ (b * b')).choose_spec
      (spinorRel_mul Q hQ (exists_spinorRel Q hQ b).choose_spec (exists_spinorRel Q hQ b').choose_spec))

/-- $\sigma(b)$ is the class of any idèle representing it. -/
theorem spinorIdeleHom_eq {b : soAf Q} {x : J} (h : SpinorRel Q hQ b x) :
    spinorIdeleHom Q hQ b = QuotientGroup.mk x := by
  change QuotientGroup.mk _ = _
  rw [QuotientGroup.eq]
  exact Subgroup.mem_sup_right (inv_mul_mem_sigmaD_of_spinorRel Q hQ (exists_spinorRel Q hQ b).choose_spec h)

end Sigma

end QuadFormsKB.Hanke2005.SpinorIdele
