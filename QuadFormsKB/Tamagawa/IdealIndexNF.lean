/-
# The index of a left ideal in a maximal order, for every class number

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$ ($ab \ne 0$), $\mathcal O \subset D$ a maximal $\mathcal O_F$-order, $J \subseteq \mathcal O$ a left
ideal with $\operatorname{nrd}(J) = \mathfrak n \ne 0$. The PID file `QuatIdealIndex` states $(\det B) = \operatorname{nrd}(J)^2$ for the coordinate matrix $B$ of an
$\mathcal O_F$-basis of $J$ in an $\mathcal O_F$-basis of $\mathcal O$. Neither basis exists for $h_F > 1$. The basis-free statement is
$$\#(\mathcal O/J) = N(\operatorname{nrd}J)^2\qquad(\texttt{Gen.card\_quot\_ideal}).$$

*Proof.* (1) A generic lemma (`card_quot_range_eq`): for an injective endomorphism $f$ of a finite free module over a PID $R$ whose principal-ideal
quotients have multiplicative cardinality, $\#(M/fM) = \#(R/\det f)$ (Smith normal form). (2) Locally, $J_v = \mathcal O_v\alpha$ (local principality) and the
right multiplication by $\alpha$ on $\mathcal O_v \cong \mathfrak o_v^4$ (a local frame) has determinant $\operatorname{nrd}(\alpha)^2$, so
$\#(\mathcal O_v/J_v) = N\mathfrak p_v^{2c_v}$. (3) CRT: $\mathcal O/J \simeq \prod_{v\mid n}\mathcal O_v/J_v$.

Sources: Voight, *Quaternion Algebras* (2021), (16.4.10), Prop. 16.4.3, Lemma 9.5.3, Thm. 9.4.9.
-/
import QuadFormsKB.Tamagawa.IdealLocalGlobalNF
import QuadFormsKB.Tamagawa.QuatIdealIndex
import QuadFormsKB.Tamagawa.QuatZetaEulerNF
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

open NumberField IsDedekindDomain Quaternion Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

section Generic

variable {R M ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι]

/-- **The cokernel of an injective endomorphism of a free module over a PID** has cardinality
$\#(R/\det f)$, provided $x \mapsto \#(R/x)$ is multiplicative on nonzero elements. -/
theorem card_quot_range_eq (hmul : ∀ x y : R, x ≠ 0 → y ≠ 0 →
      Nat.card (R ⧸ Ideal.span {x * y}) = Nat.card (R ⧸ Ideal.span {x}) * Nat.card (R ⧸ Ideal.span {y}))
    (b : Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (R ⧸ Ideal.span {LinearMap.det f}) := by
  classical
  set N := LinearMap.range f with hN
  have h : Module.finrank R N = Module.finrank R M :=
    (LinearEquiv.ofInjective f hf).symm.finrank_eq
  set a := Submodule.smithNormalFormCoeffs b h
  set b' := Submodule.smithNormalFormTopBasis b h
  set ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  have ha0 : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  have hdet : Associated (LinearMap.det f) (LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N))) := by
    have := LinearMap.associated_det_comp_equiv N.subtype e e'
    have hfe : N.subtype ∘ₗ (e : M →ₗ[R] N) = f := LinearMap.ext fun x => rfl
    rwa [hfe] at this
  have hdiag : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, a i := by
    set g : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
    have ha : ∀ i, g (b' i) = a i • b' i := fun i => by
      show (b'.equiv ab (Equiv.refl _) (b' i) : M) = _
      rw [b'.equiv_apply, Equiv.refl_apply]
      exact ab_eq i
    rw [← LinearMap.det_toMatrix b' g]
    have : LinearMap.toMatrix b' b' g = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
      by_cases hij : i = j
      · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
      · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [this, Matrix.det_diagonal]
  have hspan : Ideal.span {LinearMap.det f} = Ideal.span {∏ i, a i} := by
    rw [Ideal.span_singleton_eq_span_singleton.2 (hdet.trans (by rw [hdiag]))]
  rw [hspan, Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  have hprod : ∀ s : Finset ι, Nat.card (R ⧸ Ideal.span {∏ i ∈ s, a i}) =
      ∏ i ∈ s, Nat.card (R ⧸ Ideal.span {a i}) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Ideal.span_singleton_one]
      exact Nat.card_of_subsingleton 0
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, hmul _ _ (ha0 i) (Finset.prod_ne_zero_iff.2 fun j _ => ha0 j), ih]
  exact (hprod Finset.univ).symm

end Generic


/-! ### The local count -/

namespace Gen

section LocalCount

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) (QuatF F a b)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "Ov" => localOrder (v := v) a b O

/-- Cardinality of $\mathfrak o_v/(x)$ is multiplicative. -/
theorem card_quot_mul (x y : 𝔬) (hx : x ≠ 0) (hy : y ≠ 0) :
    Nat.card (𝔬 ⧸ Ideal.span {x * y}) = Nat.card (𝔬 ⧸ Ideal.span {x}) * Nat.card (𝔬 ⧸ Ideal.span {y}) := by
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx (irreducible_π v)
  obtain ⟨l, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy (irreducible_π v)
  have e : ∀ (z : 𝔬ˣ) (m : ℕ), Ideal.span {(z : 𝔬) * π v ^ m} = Ideal.span {π v ^ m} := fun z m =>
    Ideal.span_singleton_eq_span_singleton.2 (associated_unit_mul_left _ _ z.isUnit)
  have e2 : (u : 𝔬) * π v ^ k * ((w : 𝔬) * π v ^ l) = ((u * w : 𝔬ˣ) : 𝔬) * π v ^ (k + l) := by
    push_cast; ring
  rw [e2, e, e, e, card_quot_π_pow, card_quot_π_pow, card_quot_π_pow, pow_add]

/-- **Local principality** of left ideals of $\mathcal O_v$ with nonzero reduced norm, no PID hypothesis. -/
theorem exists_localIdeal_eq_rTrans_nf (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (I : Ideal (localOrder (v := v) a b O)) (hI : leftNrdIdeal I ≠ ⊥) :
    ∃ α : QuatV v a b, nrd α ≠ 0 ∧ idealSet I = rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) α := by
  rcases localOrder_ramified_or_split_nf (v := v) ha hb hO with ⟨hdiv, heq⟩ | ⟨φ, hφ⟩
  · exact exists_eq_rTrans_of_valOrder hdiv _ heq I hI
  · exact exists_eq_rTrans_of_map_eq_matOrder φ _ hφ I hI

/-- A frame basis of $\mathcal O_v$ over $\mathfrak o_v$. -/
def frameBasis (L : LocFrame v O) : Module.Basis (Fin 4) 𝔬 (localOrder (v := v) a b O) :=
  Module.Basis.mk (v := fun i => (⟨L.cvec i, mem_localOrder_of_mem a b (L.mem i)⟩ : localOrder (v := v) a b O))
    (by
      have h : LinearIndependent 𝔬 L.cb :=
        L.cb.linearIndependent.restrict_scalars' 𝔬
      refine LinearIndependent.of_comp (localOrder (v := v) a b O).val.toLinearMap ?_
      convert h using 1
      funext i; simp only [Function.comp_apply, LocFrame.cb_apply]; rfl)
    (by
      intro y _
      have hy := (L.mem_localOrder_iff (y : QuatV v a b)).1 y.2
      choose d hd using hy
      have : y = ∑ i, d i • (⟨L.cvec i, mem_localOrder_of_mem a b (L.mem i)⟩ : localOrder (v := v) a b O) := by
        apply Subtype.ext
        rw [← L.cb.sum_repr (y : QuatV v a b)]
        simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hd i, algebraMap_smul, LocFrame.cb_apply]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simp⟩))

theorem frameBasis_coe (L : LocFrame v O) (i : Fin 4) :
    ((frameBasis L i : localOrder (v := v) a b O) : QuatV v a b) = L.cb i := by
  rw [frameBasis, Module.Basis.mk_apply, LocFrame.cb_apply]

theorem repr_frame (L : LocFrame v O) (z : localOrder (v := v) a b O) (k : Fin 4) :
    L.cb.repr (z : QuatV v a b) k = algebraMap 𝔬 Fv ((frameBasis L).repr z k) := by
  have hz : (z : QuatV v a b) = ∑ i, algebraMap 𝔬 Fv ((frameBasis L).repr z i) • L.cb i := by
    conv_lhs => rw [← (frameBasis L).sum_repr z]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Subalgebra.coe_smul, frameBasis_coe, algebraMap_smul]
  rw [hz, Module.Basis.repr_sum_self]

set_option maxHeartbeats 1600000 in
/-- **The local index**: $\#(\mathcal O_v/I) = (N\mathfrak p_v)^{2c}$ for a left ideal $I$ of the maximal local order
with $\operatorname{nrd}(I) = (\varpi_v^c)$. -/
theorem card_quot_localIdeal (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (I : Ideal (localOrder (v := v) a b O)) {c : ℕ} (hI : leftNrdIdeal I = Ideal.span {π v ^ c}) :
    Nat.card (localOrder (v := v) a b O ⧸ I) = Ideal.absNorm v.asIdeal ^ (2 * c) := by
  classical
  have hπ0 : π v ^ c ≠ 0 := pow_ne_zero _ (irreducible_π v).ne_zero
  have hI0 : leftNrdIdeal I ≠ ⊥ := by rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact hπ0
  obtain ⟨α, hα0, hIα⟩ := exists_localIdeal_eq_rTrans_nf ha hb hO I hI0
  obtain ⟨L⟩ := LocFrame.exists (v := v) hO.1
  have hOv : IsOrder 𝔬 Fv Ov := L.isOrder_localOrder
  have hαO : α ∈ Ov := by
    have : α ∈ idealSet I := by rw [hIα]; exact ⟨1, Subalgebra.one_mem _, one_mul α⟩
    exact idealSet_subset I this
  obtain ⟨t, ht⟩ := (isInteger_trd_nrd hOv hαO).2
  have hIt : leftNrdIdeal I = Ideal.span {t} :=
    leftNrdIdeal_eq_of_idealSet_eq_rTrans (IsFractionRing.injective _ _)
      (fun y hy => (isInteger_trd_nrd hOv hy).2) hIα ht
  have hαu : IsUnit α := (isUnit_iff_nrd_ne_zero α).2 hα0
  let f : Ov →ₗ[𝔬] Ov :=
    { toFun := fun x => ⟨(x : QuatV v a b) * α, Subalgebra.mul_mem _ x.2 hαO⟩
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r x => Subtype.ext (by
        show ((r • x : localOrder (v := v) a b O) : QuatV v a b) * α = r • ((x : QuatV v a b) * α)
        rw [Subalgebra.coe_smul, smul_mul_assoc]) }
  have hf : ∀ x, ((f x : Ov) : QuatV v a b) = (x : QuatV v a b) * α := fun x => rfl
  have hinj : Function.Injective f := fun x y hxy => by
    have := congrArg Subtype.val hxy
    rw [hf, hf] at this
    exact Subtype.ext (hαu.mul_left_inj.1 this)
  have hrange : LinearMap.range f = I.restrictScalars 𝔬 := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      have : ((f x : Ov) : QuatV v a b) ∈ idealSet I := by
        rw [hIα, hf]; exact ⟨x, x.2, rfl⟩
      obtain ⟨h1, h2⟩ := this
      exact h2
    · intro hz
      have : (z : QuatV v a b) ∈ idealSet I := ⟨z.2, hz⟩
      rw [hIα] at this
      obtain ⟨y, hy, hyz⟩ := this
      exact ⟨⟨y, hy⟩, Subtype.ext (by rw [hf]; exact hyz)⟩
  have hM : (RingHom.mapMatrix (algebraMap 𝔬 Fv)) (LinearMap.toMatrix (frameBasis L) (frameBasis L) f) =
      LinearMap.toMatrix L.cb L.cb (LinearMap.mulRight Fv α) := by
    ext k i
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    rw [← repr_frame L (f (frameBasis L i)) k, hf, frameBasis_coe]
    rfl
  have hdet : algebraMap 𝔬 Fv (LinearMap.det f) = nrd α ^ 2 := by
    have h2 : (LinearMap.toMatrix (frameBasis L) (frameBasis L) f).det = LinearMap.det f :=
      LinearMap.det_toMatrix (frameBasis L) f
    have h1 : algebraMap 𝔬 Fv (LinearMap.det f) = ((RingHom.mapMatrix (algebraMap 𝔬 Fv))
        (LinearMap.toMatrix (frameBasis L) (frameBasis L) f)).det := by
      rw [← h2]; exact RingHom.map_det _ _
    rw [h1, hM, LinearMap.det_toMatrix, det_mulRight]
  have hdt : LinearMap.det f = t ^ 2 := by
    apply IsFractionRing.injective 𝔬 Fv
    rw [hdet, map_pow, ht]
  have hcard1 : Nat.card (Ov ⧸ I) = Nat.card (Ov ⧸ I.restrictScalars 𝔬) :=
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv 𝔬 I).symm.toEquiv
  have hcard2 : Nat.card (Ov ⧸ LinearMap.range f) = Nat.card (𝔬 ⧸ Ideal.span {LinearMap.det f}) :=
    card_quot_range_eq (fun x y hx hy => card_quot_mul x y hx hy) (frameBasis L) f hinj
  rw [hcard1, ← hrange, hcard2, hdt]
  have hspan : Ideal.span {t} = Ideal.span {π v ^ c} := hIt.symm.trans hI
  have hspan2 : Ideal.span {t ^ 2} = Ideal.span {π v ^ (2 * c)} := by
    rw [← Ideal.span_singleton_pow, hspan, Ideal.span_singleton_pow, ← pow_mul, mul_comm]
  rw [hspan2]
  exact card_quot_π_pow v (2 * c)

end LocalCount

end Gen

/-! ### The global-to-local quotient -/

namespace Gen

section Global

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

theorem toLocal_smul (w : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (z : O) :
    toLocal w (r • z) = ι w r • toLocal (a := a) (b := b) (O := O) w z := by
  apply Subtype.ext
  rw [coe_toLocal, Subalgebra.coe_smul, Subalgebra.coe_smul, coe_toLocal]
  erw [complHom_int_smul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Approximation (CRT, basis-free):** for any local targets $y_v \in \mathcal O_v$ ($v \mid n$) there is a global $x \in \mathcal O$
with $\iota_v(x) - y_v \in J_v$ for all $v \mid n$, as soon as $n \in J$. -/
theorem exists_global_approx (hO : IsOrder (𝓞 F) F O) {n : 𝓞 F} (hn : n ≠ 0) {J : Ideal O}
    (hnJ : algebraMap (𝓞 F) O n ∈ J)
    (y : ∀ v : primeSupport hn, localOrder (v := v.1) a b O) :
    ∃ x : O, ∀ v : primeSupport hn, toLocal v.1 x - y v ∈ localIdeal (v := v.1) J := by
  classical
  let L : ∀ v : HeightOneSpectrum (𝓞 F), LocFrame v O := fun v => (LocFrame.exists (v := v) hO).some
  let e : HeightOneSpectrum (𝓞 F) → ℕ := fun u => cI u (Ideal.span {n})
  let E : ∀ (v w : HeightOneSpectrum (𝓞 F)) (i : Fin 4), localOrder (v := w) a b O := fun v w i =>
    ⟨complHom w a b ((L v).fb i : QuatF F a b), mem_localOrder_of_mem a b ((L v).mem i)⟩
  -- coordinates of the targets
  have hcoord : ∀ v : primeSupport hn, ∃ d : Fin 4 → v.1.adicCompletionIntegers F,
      y v = ∑ i, d i • E v.1 v.1 i := by
    intro v
    have hd := ((L v.1).mem_localOrder_iff ((y v : localOrder (v := v.1) a b O) : QuatV v.1 a b)).1 (y v).2
    choose d hd using hd
    refine ⟨d, Subtype.ext ?_⟩
    rw [← (L v.1).cb.sum_repr ((y v : localOrder (v := v.1) a b O) : QuatV v.1 a b),
      AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Subalgebra.coe_smul, ← hd i, algebraMap_smul, LocFrame.cb_apply]; rfl
  choose d hd using hcoord
  have hap := fun (v : primeSupport hn) i => exists_ι_sub_mem_span v.1 (e v.1) (d v i)
  choose r0 hr0 using hap
  have hcrt := fun (v : primeSupport hn) => exists_crt_idem (primeSupport hn) e v.1
  choose t ht1 ht0 using hcrt
  refine ⟨∑ v : primeSupport hn, ∑ i, (t v * r0 v i) • (⟨(L v.1).fb i, (L v.1).mem i⟩ : O), fun w => ?_⟩
  have hnw : algebraMap _ (localOrder (v := w.1) a b O) (ι w.1 n) ∈ localIdeal (v := w.1) J :=
    algebraMap_mem_localIdeal w.1 hnJ
  have hloc_x : toLocal w.1 (∑ v : primeSupport hn, ∑ i, (t v * r0 v i) • (⟨(L v.1).fb i, (L v.1).mem i⟩ : O)) =
      ∑ v : primeSupport hn, ∑ i, ι w.1 (t v * r0 v i) • E v.1 w.1 i := by
    simp only [map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [toLocal_smul]
    rfl
  have hcoef : ∀ (v : primeSupport hn), v ≠ w → ∀ i, ι w.1 (t v * r0 v i) ∈ Ideal.span {ι w.1 n} := by
    intro v hvw i
    rw [span_ι_eq_cI w.1 hn, ι_mem_span_π_pow]
    exact Ideal.mul_mem_right _ _ (ht0 v w.1 w.2 (fun h => hvw (Subtype.ext h.symm)))
  have hcoefw : ∀ i, ι w.1 (t w * r0 w i) - d w i ∈ Ideal.span {ι w.1 n} := by
    intro i
    rw [span_ι_eq_cI w.1 hn]
    have e1 : ι w.1 (t w - 1) ∈ Ideal.span {π w.1 ^ e w.1} := (ι_mem_span_π_pow w.1 _ _).2 (ht1 w)
    have : ι w.1 (t w * r0 w i) - d w i = ι w.1 (t w - 1) * ι w.1 (r0 w i) - (d w i - ι w.1 (r0 w i)) := by
      simp only [map_mul, map_sub, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ e1) (hr0 w i)
  set G : primeSupport hn → localOrder (v := w.1) a b O := fun v => ∑ i, ι w.1 (t v * r0 v i) • E v.1 w.1 i with hG
  have hsplit : (∑ v : primeSupport hn, G v) = G w + ∑ v ∈ Finset.univ.erase w, G v :=
    (Finset.add_sum_erase Finset.univ G (Finset.mem_univ w)).symm
  have herase : (∑ v ∈ Finset.univ.erase w, G v) ∈ localIdeal (v := w.1) J :=
    Ideal.sum_mem _ fun v hv => Ideal.sum_mem _ fun i _ =>
      smul_mem_of_algebraMap_mem w.1 hnw (hcoef v (Finset.ne_of_mem_erase hv) i) _
  have hGw : G w - y w ∈ localIdeal (v := w.1) J := by
    rw [hd w]
    have : G w - ∑ i, d w i • E w.1 w.1 i = ∑ i, (ι w.1 (t w * r0 w i) - d w i) • E w.1 w.1 i := by
      simp only [hG]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    rw [this]
    exact Ideal.sum_mem _ fun i _ => smul_mem_of_algebraMap_mem w.1 hnw (hcoefw i) _
  rw [hloc_x]
  have h3 : (∑ v : primeSupport hn, ∑ i, ι w.1 (t v * r0 v i) • E v.1 w.1 i) - y w =
      (G w - y w) + ∑ v ∈ Finset.univ.erase w, G v := by
    show (∑ v : primeSupport hn, G v) - y w = _
    rw [hsplit]; abel
  rw [h3]
  exact Ideal.add_mem _ hGw herase

/-- $N(\mathfrak n) = \prod_{v\mid n}N\mathfrak p_v^{c_v(\mathfrak n)}$ for $0 \ne n \in \mathfrak n$. -/
theorem absNorm_eq_prod {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) {n : 𝓞 F} (hn : n ≠ 0) (hn𝔫 : n ∈ 𝔫) :
    Ideal.absNorm 𝔫 = ∏ v ∈ primeSupport hn, Ideal.absNorm v.asIdeal ^ cI v 𝔫 := by
  classical
  have hord0 : ∀ v ∉ primeSupport hn, cI v 𝔫 = 0 := fun v hv =>
    cI_eq_zero_of_mem_not_mem h𝔫 hn𝔫 fun h => hv ((mem_primeSupport hn).2 h)
  have hI0 : (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact h𝔫
  have h1 := QuadFormsKB.Tamagawa.idealNorm_eq_finprod F (Units.mk0 _ hI0)
  have h2 : QuadFormsKB.IdeleClass.idealNorm F (Units.mk0 _ hI0) = (Ideal.absNorm 𝔫 : ℝ) := by
    rw [QuadFormsKB.IdeleClass.idealNorm, Units.val_mk0, FractionalIdeal.coeIdeal_absNorm]; push_cast; rfl
  have e3 : (Ideal.absNorm 𝔫 : ℝ) = ∏ v ∈ primeSupport hn, (Ideal.absNorm v.asIdeal : ℝ) ^ cI v 𝔫 := by
    rw [← h2, h1]
    simp_rw [Units.val_mk0, count_coe_eq_cI _ h𝔫, zpow_natCast]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS; apply hv
    show (Ideal.absNorm v.asIdeal : ℝ) ^ cI v 𝔫 = 1
    rw [hord0 v hvS, pow_zero]
  exact_mod_cast e3

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **The index of a left ideal of a maximal order, for every class number:**
$\#(\mathcal O/J) = N(\operatorname{nrd}J)^2$ ($ab \ne 0$, $\operatorname{nrd}J \ne 0$). No basis of $\mathcal O$, $J$, or any ideal is used.

Source: Voight 2021, (16.4.10) / Prop. 16.4.3 (index = norm squared of the reduced norm), via the local-global principle of Thm. 9.4.9. -/
@[kb "voight2021" "(16.4.10)"]
theorem card_quot_ideal (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) : Nat.card (O ⧸ J) = Ideal.absNorm (leftNrdIdeal J) ^ 2 := by
  classical
  set 𝔫 := leftNrdIdeal J with h𝔫def
  obtain ⟨n, hn𝔫, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hnJ : algebraMap (𝓞 F) O n ∈ J := algebraMap_mem_of_mem_leftNrdIdeal hO.1 J hn𝔫
  have hker : ∀ x : O, (∀ v : primeSupport hn, toLocal v.1 x ∈ localIdeal (v := v.1) J) → x ∈ J := by
    intro x hxv
    have hle : Ideal.span {x} ≤ J := by
      refine le_of_localIdeal_le hO.1 hn hnJ fun v hv => ?_
      intro z hz
      rw [mem_localIdeal_iff] at hz ⊢
      refine Submodule.span_le.2 ?_ hz
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have h1 := (localIdeal (v := v) J).mul_mem_left (toLocal v c) (hxv ⟨v, hv⟩)
      rw [mem_localIdeal_iff] at h1
      show ((toLocal v (c * x) : localOrder (v := v) a b O) : QuatV v a b) ∈
        Submodule.span (v.adicCompletionIntegers F) (idealImage (v := v) J)
      rw [map_mul]
      exact h1
    exact hle (Ideal.subset_span rfl)
  let Ψ : (O ⧸ J) → ((v : primeSupport hn) → (localOrder (v := v.1) a b O ⧸ localIdeal (v := v.1) J)) :=
    Quotient.lift (s := Submodule.quotientRel J) (fun x (v : primeSupport hn) => Submodule.Quotient.mk (toLocal v.1 x)) (by
      intro x x' hxx'
      funext v
      rw [Submodule.Quotient.eq, ← map_sub]
      exact toLocal_mem_localIdeal v.1 ((Submodule.quotientRel_def J).1 hxx'))
  have hΨ : ∀ x : O, Ψ (Submodule.Quotient.mk x) = fun (v : primeSupport hn) => Submodule.Quotient.mk (toLocal v.1 x) := fun x => rfl
  have hinj : Function.Injective Ψ := by
    intro q q'
    induction q using Submodule.Quotient.induction_on with | _ x
    induction q' using Submodule.Quotient.induction_on with | _ x'
    intro h
    rw [hΨ, hΨ] at h
    rw [Submodule.Quotient.eq]
    refine hker _ fun v => ?_
    rw [map_sub]
    exact (Submodule.Quotient.eq _).1 (congrFun h v)
  have hsurj : Function.Surjective Ψ := by
    intro u
    obtain ⟨x, hx⟩ := exists_global_approx hO.1 hn hnJ fun v => (u v).out
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [hΨ]
    funext v
    rw [← Quotient.out_eq (u v)]
    exact (Submodule.Quotient.eq _).2 (hx v)
  rw [Nat.card_congr (Equiv.ofBijective Ψ ⟨hinj, hsurj⟩), Nat.card_pi]
  have hloc : ∀ v : primeSupport hn,
      Nat.card (localOrder (v := v.1) a b O ⧸ localIdeal (v := v.1) J) = Ideal.absNorm v.1.asIdeal ^ (2 * cI v.1 𝔫) := by
    intro v
    refine card_quot_localIdeal ha hb hO _ ?_
    rw [leftNrdIdeal_localIdeal hO.1, map_ι_eq_span v.1 hJ]
  simp_rw [hloc]
  rw [absNorm_eq_prod hJ hn hn𝔫, ← Finset.prod_pow, ← Finset.prod_coe_sort (primeSupport hn)]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← pow_mul, mul_comm]


end Global

end Gen

end QuadFormsKB.QuatOrder
