/-
# Kneser neighbours over $\mathcal O_F$, part 4: good primes of a number field and genus mates

**Layer:** $F$ a number field, $Q$ a form over $\mathcal O_F$ (`QuadForm (𝓞 F) n`), $\pi$ a prime element of $\mathcal O_F$ with
$\pi \nmid 2\det H$ (a good prime $\mathfrak p = (\pi)$, $q = N\mathfrak p$ = `nm π`), $v_\pi$ = `hosOf π` the corresponding finite place.

**Proves**
- the residue field $k = \mathcal O_F/\pi$ is a finite field of size $q$ and odd characteristic (`isMaximal_span`, `finite_res`,
  `card_res`, `ringChar_res_ne_two`);
- **Table 1 mod $\pi$** for even $n$ (Hanke 2004, Table 1, p. 363, via `LocalDensity.NF.card_mod_p_of_unimodular`):
  $\#\{\bar Q = 0\} = q^{n-1} + \chi_\pi(q-1)q^{n/2-1}$ and $\#\{\bar Q = c\} = q^{n-1} - \chi_\pi q^{n/2-1}$ for $c \ne 0$, with
  $\chi_\pi = \chi\big((-1)^{n/2}\det H/2^n\big)$ = `chiPi Q π` (`card_qv_zero_res`, `card_qv_ne_zero_res`);
- **the neighbour relation over $F$** (`sum_latRep_neighbors_F`): for $Q$ totally positive definite, $n$ even, $\pi \nmid 2\det H$,
  $\pi \nmid m$,
  $$(q - 1)\sum_{L' \sim_\pi \mathcal O_F^n} r_{L'}(m) = (q-1)\,r_Q(\pi^2m) + (q^{n-2} - q)\,r_Q(m),$$
  and the number of neighbours (`card_neighbors_F`): $(q - 1)\cdot\#\{L'\} = q^{n-1} - 1 + \chi_\pi(q-1)q^{n/2-1}$;
- **genus mates have the same counts mod $\pi$** (`card_qv_eq_of_formSameGenus`): if $Q' \in \mathrm{gen}(Q)$ then
  $\#\{\bar Q' = c\} = \#\{\bar Q = c\}$ for every $c$, and $\pi \nmid \det H'$ (`not_dvd_det_of_formSameGenus`). So all classes of a genus
  have the same number of $\pi$-neighbours and the same $\chi_\pi$.
-/
import QuadFormsKB.Lattices.NeighborRep
import QuadFormsKB.LocalDensity.NFLocalGeneral
import QuadFormsKB.HilbertModular.HeckeVanishing
import QuadFormsKB.Lattices.Forms
import QuadFormsKB.Lattices.FreeBridge

open Matrix NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

attribute [local instance] Ideal.Quotient.field

namespace QuadFormsKB.Lattices.Nbr

open QuadFormsKB.LocalDensity QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Local

variable {π : 𝓞 F} (hπ : Prime π)
include hπ

lemma span_ne_bot : Ideal.span {π} ≠ ⊥ := by simpa using hπ.ne_zero

/-- The finite place $v_\pi$ of the prime $(\pi)$. -/
noncomputable def hosOf : HeightOneSpectrum (𝓞 F) :=
  ⟨Ideal.span {π}, (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ, span_ne_bot hπ⟩

@[simp] lemma hosOf_asIdeal : (hosOf hπ).asIdeal = Ideal.span {π} := rfl

lemma isMaximal_span : (Ideal.span {π}).IsMaximal :=
  ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal (span_ne_bot hπ)

lemma finite_res : Finite (Res π) := Ideal.finiteQuotientOfFreeOfNeBot _ (span_ne_bot hπ)

omit hπ in
/-- $|k| = N(\pi)$. -/
lemma card_res [Fintype (Res π)] : Fintype.card (Res π) = nm π := by
  rw [nm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

/-- $\operatorname{char}k \ne 2$ for $\pi \nmid 2$. -/
lemma ringChar_res_ne_two (h2 : ¬ π ∣ 2) :
    letI := isMaximal_span hπ
    ringChar (Res π) ≠ 2 := by
  letI := isMaximal_span hπ
  intro h
  have h2' : (2 : Res π) = 0 := by
    have := ringChar.spec (Res π) 2
    rw [h] at this; exact_mod_cast this.mpr dvd_rfl
  apply h2
  rw [← dvd_of_red, map_ofNat]; exact h2'

/-- **Counts mod $\pi$ are the counts of Hanke's §2** (`LocalDensity.NF.repCount` at $v_\pi$, level $1$). -/
lemma card_filter_qv_eq_repCount [Fintype (Res π)] [DecidableEq (Res π)] (Q : QuadForm (𝓞 F) n)
    (m : 𝓞 F) :
    (Finset.univ.filter fun y : Fin n → Res π => qv (Res π) Q y = Ideal.Quotient.mk _ m).card =
      NF.repCount (hosOf hπ) Q 1 m := by
  classical
  have hI : (hosOf hπ).asIdeal ^ 1 = Ideal.span {π} := by rw [pow_one]; rfl
  set e := Ideal.quotEquivOfEq hI
  rw [NF.repCount, ← Nat.card_eq_finsetCard]
  refine (Nat.card_congr ((Equiv.piCongrRight fun _ => e.toEquiv).subtypeEquiv fun x => ?_)).symm
  have hmk : ∀ a : 𝓞 F, e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := fun a => rfl
  rw [← e.injective.eq_iff, hmk]
  simp only [qv, QuadForm.evalIn, map_sum, apply_ite e, map_mul, map_zero, Ideal.Quotient.algebraMap_eq,
    hmk]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

end Local

/-- **The local character at $\pi$** of an even-rank form: $\chi_\pi = \chi\big((-1)^{n/2}\det H/2^n\big)$, $\chi$ the quadratic character of
$k = \mathcal O_F/\pi$ (`LocalDensity.DVR.chiDisc` of $Q \otimes \mathfrak o_\pi$; Hanke 2004, $\Phi_n(\mathfrak p)$, p. 357). -/
noncomputable def chiPi (Q : QuadForm (𝓞 F) n) {π : 𝓞 F} (hπ : Prime π) : ℤ :=
  DVR.chiDisc (NF.Qp (hosOf hπ) Q)

section Table1

variable {π : 𝓞 F} (hπ : Prime π) {Q : QuadForm (𝓞 F) n}
include hπ

lemma two_not_mem (h2 : ¬ π ∣ 2) : (2 : 𝓞 F) ∉ (hosOf hπ).asIdeal := by
  rw [hosOf_asIdeal, Ideal.mem_span_singleton]; exact h2

lemma det_not_mem (hdet : ¬ π ∣ Q.hessian.det) : Q.hessian.det ∉ (hosOf hπ).asIdeal := by
  rw [hosOf_asIdeal, Ideal.mem_span_singleton]; exact hdet

/-- **Table 1 mod $\pi$, $n$ even** ($\pi \nmid 2\det H$, $q = N(\pi)$, $\chi_\pi$ = `chiPi`): $\#\{\bar Q = 0\} = q^{n-1} + \chi_\pi(q-1)q^{n/2-1}$. -/
@[kb "hanke2004" "Table 1, p. 363 (mod 𝔭, over F, n even)"]
theorem card_qv_zero_res [Fintype (Res π)] [DecidableEq (Res π)] (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : Even n) (hn1 : 1 ≤ n) :
    ((Finset.univ.filter fun y : Fin n → Res π => qv (Res π) Q y = 0).card : ℤ) =
      (nm π : ℤ) ^ (n - 1) + chiPi Q hπ * ((nm π : ℤ) - 1) * (nm π : ℤ) ^ (n / 2 - 1) := by
  have hN := (NF.notDvdLevel_iff (hosOf hπ) Q (two_not_mem hπ h2)).mpr (det_not_mem hπ hdet)
  have h := ((NF.card_mod_p_of_unimodular (hosOf hπ) Q (two_not_mem hπ h2) hN hn1 1 (by
    rw [hosOf_asIdeal, Ideal.mem_span_singleton]; exact hπ.not_dvd_one)).1 hn).1
  rw [← map_zero (Ideal.Quotient.mk (Ideal.span {π})), card_filter_qv_eq_repCount hπ]
  exact h

/-- **Table 1 mod $\pi$, $n$ even, nonzero values**: $\#\{\bar Q = c\} = q^{n-1} - \chi_\pi q^{n/2-1}$ for $c \ne 0$. -/
@[kb "hanke2004" "Table 1, p. 363 (mod 𝔭, over F, n even)"]
theorem card_qv_ne_zero_res [Fintype (Res π)] [DecidableEq (Res π)] (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : Even n) (hn1 : 1 ≤ n) {c : Res π} (hc : c ≠ 0) :
    ((Finset.univ.filter fun y : Fin n → Res π => qv (Res π) Q y = c).card : ℤ) =
      (nm π : ℤ) ^ (n - 1) - chiPi Q hπ * (nm π : ℤ) ^ (n / 2 - 1) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hu : u ∉ (hosOf hπ).asIdeal := by
    rw [hosOf_asIdeal]; intro h; exact hc (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hN := (NF.notDvdLevel_iff (hosOf hπ) Q (two_not_mem hπ h2)).mpr (det_not_mem hπ hdet)
  have h := ((NF.card_mod_p_of_unimodular (hosOf hπ) Q (two_not_mem hπ h2) hN hn1 u hu).1 hn).2
  rw [card_filter_qv_eq_repCount hπ]
  exact h

end Table1

section FormRelation

variable {π : 𝓞 F} (hπ : Prime π) {Q : QuadForm (𝓞 F) n}
include hπ

/-- **The neighbour relation over $\mathcal O_F$** at a good prime $\pi \nmid 2\det H$, $\pi \nmid m$, $n$ even, $Q$ totally positive definite:
$$(q - 1)\sum_{L' \sim_\pi \mathcal O_F^n} r_{L'}(m) = (q-1)\,r_Q(\pi^2m) + (q^{n-2} - q)\,r_Q(m),\qquad q = N(\pi).$$
(`sum_latRep_neighbors_of_not_dvd` with Table 1 for `hconst`.) -/
@[kb "eichler1952" "Eichler commutation relation over F, π ∤ m [unverified]"]
theorem sum_latRep_neighbors_F [IsTotallyReal F] [Fintype (Res π)] [DecidableEq (Res π)]
    (hQ : HilbertModular.IsTotPosGram (HilbertModular.gramF Q)) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : Even n) (hn2 : 2 ≤ n) {m : 𝓞 F} (hm : ¬ π ∣ m) :
    ((nm π : ℤ) - 1) * ∑ L ∈ neighbors F Q π, (latRep F Q L m : ℤ) =
      ((nm π : ℤ) - 1) * repNum Q (π ^ 2 * m) + ((nm π : ℤ) ^ (n - 2) - nm π) * repNum Q m := by
  have := isMaximal_span hπ
  have hfin : ∀ M : 𝓞 F, Set.Finite {y : Fin n → 𝓞 F | qv (𝓞 F) Q y = M} :=
    fun M => HilbertModular.finite_repSetF hQ M
  have hconst : ∀ c : Res π, c ≠ 0 → (Finset.univ.filter fun y => qv (Res π) Q y = c).card =
      (Finset.univ.filter fun y => qv (Res π) Q y = 1).card := by
    intro c hc
    have h1 := card_qv_ne_zero_res hπ h2 hdet hn (by omega) hc
    have h2' := card_qv_ne_zero_res (Q := Q) hπ h2 hdet hn (by omega) (one_ne_zero (α := Res π))
    exact_mod_cast h1.trans h2'.symm
  have h := sum_latRep_neighbors_of_not_dvd (K := F) hfin hπ (ringChar_res_ne_two hπ h2) hdet hn2 hconst hm
  rw [card_res] at h
  exact h

/-- **The number of $\pi$-neighbours over $\mathcal O_F$** ($n$ even, $\pi \nmid 2\det H$): with $q = N(\pi)$,
$$(q - 1)\cdot\#\{L' \sim_\pi \mathcal O_F^n\} = q^{n-1} - 1 + \chi_\pi(q - 1)q^{n/2-1},$$
i.e. $\#\{L'\} = \frac{q^{n-1}-1}{q-1} + \chi_\pi q^{n/2-1}$ (the isotropic lines of $L/\pi L$). -/
@[kb "kneser1957" "§1, number of 𝔭-neighbours (over F) [unverified]"]
theorem card_neighbors_F [Fintype (Res π)] [DecidableEq (Res π)] (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : Even n) (hn1 : 1 ≤ n) :
    ((nm π : ℤ) - 1) * (neighbors F Q π).card =
      (nm π : ℤ) ^ (n - 1) - 1 + chiPi Q hπ * ((nm π : ℤ) - 1) * (nm π : ℤ) ^ (n / 2 - 1) := by
  have := isMaximal_span hπ
  have h1 := card_neighbors (K := F) hπ hdet (Q := Q)
  have h2' := card_isoSet (Q := Q) (π := π)
  have h3 := card_qv_zero_res (Q := Q) hπ h2 hdet hn hn1
  have hq1 : 1 ≤ Fintype.card (Res π) := Fintype.card_pos
  rw [card_res] at h1 hq1
  have e1 : (((nm π - 1) * (neighbors F Q π).card : ℕ) : ℤ) = ((isoSet Q π).card : ℤ) := by rw [h1]
  push_cast [Nat.cast_sub hq1] at e1
  rw [e1]
  have e2 : (((isoSet Q π).card + 1 : ℕ) : ℤ) = _ := congrArg (fun t : ℕ => (t : ℤ)) h2'
  push_cast at e2
  linear_combination e2 + h3

end FormRelation

/-! ### Genus mates have the same counts mod $\pi$ -/

section GenusMates

variable {π : 𝓞 F} (hπ : Prime π) {Q Q' : QuadForm (𝓞 F) n}
include hπ

/-- A $\mathrm{GL}_n(\mathfrak o_\pi)$-isometry gives a `DVR.IsGLEquiv`. -/
lemma isGLEquiv_of_formSameGenus (h : FormSameGenus Q Q') :
    DVR.IsGLEquiv (NF.Qp (hosOf hπ) Q) (NF.Qp (hosOf hπ) Q') := by
  obtain ⟨g, hg⟩ := h.1 (hosOf hπ)
  exact ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, fun x => (hg x).symm⟩

/-- **Genus mates have the same counts mod $\pi$:** $\#\{\bar Q' = c\} = \#\{\bar Q = c\}$ for every $c \in k$. -/
theorem card_qv_eq_of_formSameGenus [Fintype (Res π)] [DecidableEq (Res π)] (h : FormSameGenus Q Q')
    (c : Res π) :
    (Finset.univ.filter fun y : Fin n → Res π => qv (Res π) Q' y = c).card =
      (Finset.univ.filter fun y : Fin n → Res π => qv (Res π) Q y = c).card := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [card_filter_qv_eq_repCount hπ, card_filter_qv_eq_repCount hπ, NF.repCount_eq_completion,
    NF.repCount_eq_completion, (isGLEquiv_of_formSameGenus hπ h).repCount_eq]

/-- **Genus mates are unimodular at the same primes:** $\pi \nmid \det H \Rightarrow \pi \nmid \det H'$. -/
theorem not_dvd_det_of_formSameGenus (h : FormSameGenus Q Q') (hdet : ¬ π ∣ Q.hessian.det) :
    ¬ π ∣ Q'.hessian.det := by
  obtain ⟨u, hu, he⟩ := (isGLEquiv_of_formSameGenus hπ h).det_hessian
  rw [NF.det_hessian_Qp, NF.det_hessian_Qp] at he
  intro hd
  apply hdet
  have h1 : NF.π (hosOf hπ) ∣ NF.ι (hosOf hπ) Q'.hessian.det := by
    rw [NF.π_dvd_ι_iff, hosOf_asIdeal, Ideal.mem_span_singleton]; exact hd
  rw [he] at h1
  have h2 : NF.π (hosOf hπ) ∣ NF.ι (hosOf hπ) Q.hessian.det :=
    (hu.pow 2).dvd_mul_left.mp h1
  rwa [NF.π_dvd_ι_iff, hosOf_asIdeal, Ideal.mem_span_singleton] at h2

/-- Genus mates have the same local character $\chi_\pi$ ($n$ even, $\pi \nmid 2\det H$): compare Table 1 at $0$. -/
theorem chiPi_eq_of_formSameGenus (h : FormSameGenus Q Q') (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q.hessian.det)
    (hn : Even n) (hn2 : 2 ≤ n) : chiPi Q' hπ = chiPi Q hπ := by
  classical
  have := finite_res hπ
  letI := Fintype.ofFinite (Res π)
  have h1 := card_qv_zero_res (Q := Q) hπ h2 hdet hn (by omega)
  have h1' := card_qv_zero_res (Q := Q') hπ h2 (not_dvd_det_of_formSameGenus hπ h hdet) hn (by omega)
  rw [card_qv_eq_of_formSameGenus hπ h] at h1'
  have hq : 1 < nm π := by
    have h1 : nm π ≠ 1 := fun h => hπ.not_isUnit ((nm_eq_one_iff π).mp h)
    have h0 : nm π ≠ 0 := by
      rw [nm, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hπ.ne_zero
    omega
  have hq' : ((nm π : ℤ) - 1) * (nm π : ℤ) ^ (n / 2 - 1) ≠ 0 := by
    apply mul_ne_zero
    · have : (1 : ℤ) < nm π := by exact_mod_cast hq
      linarith
    · exact pow_ne_zero _ (by exact_mod_cast (by omega : nm π ≠ 0))
  have := h1.symm.trans h1'
  have h3 : (chiPi Q' hπ - chiPi Q hπ) * (((nm π : ℤ) - 1) * (nm π : ℤ) ^ (n / 2 - 1)) = 0 := by
    linear_combination -this
  have := (mul_eq_zero.mp h3).resolve_right hq'
  linarith

end GenusMates

/-! ### Neighbours of lattices in $F^n$ -/

section LatNbr

variable (Q : QuadForm F n)

/-- **$\pi$-neighbours of an $\mathcal O_F$-lattice** $M \subseteq F^n$ (Kneser 1957, §1; O'Meara 1963, §82 for the lattice language),
coordinate-free: $M'$ with
$$[M : M \cap M'] = q,\quad [M' : M \cap M'] = q,\quad \pi M' \subseteq M,\quad \pi M \subseteq M',\quad Q(M), Q(M') \subseteq \mathcal O_F,$$
$q = N(\pi)$. Symmetric (`IsNbrL.symm`) and invariant under $O(V)(F)$ (`IsNbrL.glImage`). For $M = \gamma\mathcal O_F^n$ these are the
$\gamma L'$, $L'$ a $\pi$-neighbour of $\mathcal O_F^n$ for the Gram form $Q_\gamma$ (`isNbrL_latOf_iff`). Fields: `index_left`,
`index_right` (Mathlib's `relIndex H K` is $[K : H \cap K]$), `smul_left`, `smul_right`, `int_left`, `int_right`. -/
@[kb "kneser1957" "§1, neighbouring lattices [unverified]; omeara1963 §106B, p. 325 (adjacent lattices; the library allows any prime)"]
structure IsNbrL (π : 𝓞 F) (M M' : Submodule (𝓞 F) (Fin n → F)) : Prop where
  index_left : M'.toAddSubgroup.relIndex M.toAddSubgroup = nm π
  index_right : M.toAddSubgroup.relIndex M'.toAddSubgroup = nm π
  smul_left : ∀ x ∈ M', algebraMap (𝓞 F) F π • x ∈ M
  smul_right : ∀ x ∈ M, algebraMap (𝓞 F) F π • x ∈ M'
  int_left : IsIntegral Q M
  int_right : IsIntegral Q M'

/-- **The representation numbers of a lattice in $(F^n, Q)$**: $r_M(\nu) = \#\{x \in M : Q(x) = \nu\}$, $\nu \in \mathcal O_F$. -/
@[kb "siegel1935" "representation numbers of a lattice, over F [unverified]"]
noncomputable def latRepF (M : Submodule (𝓞 F) (Fin n → F)) (ν : 𝓞 F) : ℕ :=
  Nat.card {x : Fin n → F // x ∈ M ∧ Q.evalIn F x = algebraMap (𝓞 F) F ν}

variable {Q} {π : 𝓞 F}

theorem IsNbrL.symm {M M' : Submodule (𝓞 F) (Fin n → F)} (h : IsNbrL Q π M M') : IsNbrL Q π M' M :=
  ⟨h.2, h.1, h.4, h.3, h.6, h.5⟩

lemma toAddSubgroup_glImage (γ : GL (Fin n) F) (N : Submodule (𝓞 F) (Fin n → F)) :
    (glImage γ N).toAddSubgroup = N.toAddSubgroup.map (Matrix.mulVecLin γ.val).toAddMonoidHom := by
  ext x; simp [glImage, mem_glImage]

lemma mulVec_injective_gl (γ : GL (Fin n) F) : Function.Injective (fun x : Fin n → F => γ.val *ᵥ x) := by
  intro x y h
  have := congrArg (fun w => (γ⁻¹).val *ᵥ w) h
  simpa [mulVec_mulVec, ← Units.val_mul] using this

lemma relIndex_glImage (γ : GL (Fin n) F) (N N' : Submodule (𝓞 F) (Fin n → F)) :
    (glImage γ N').toAddSubgroup.relIndex (glImage γ N).toAddSubgroup =
      N'.toAddSubgroup.relIndex N.toAddSubgroup := by
  rw [toAddSubgroup_glImage, toAddSubgroup_glImage,
    AddSubgroup.relIndex_map_map_of_injective _ _ (mulVec_injective_gl γ)]

lemma smul_mem_glImage_iff (γ : GL (Fin n) F) (c : F) (N N' : Submodule (𝓞 F) (Fin n → F)) :
    (∀ x ∈ glImage γ N, c • x ∈ glImage γ N') ↔ ∀ x ∈ N, c • x ∈ N' := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, e⟩ := h _ (mulVec_mem_glImage hx)
    rw [← mulVec_smul] at e
    rwa [← mulVec_injective_gl γ e]
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := mem_glImage.mp hy
    rw [← mulVec_smul]; exact mulVec_mem_glImage (h x hx)

lemma glImage_injective (γ : GL (Fin n) F) : Function.Injective (glImage (n := n) γ) := by
  intro N N' h
  rw [← glImage_one N, ← glImage_one N', ← inv_mul_cancel γ, glImage_mul, glImage_mul, h]

lemma isIntegral_glImage {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) {N : Submodule (𝓞 F) (Fin n → F)} :
    IsIntegral Q (glImage γ N) ↔ IsIntegral Q N := by
  constructor
  · intro h x hx
    have := h _ (mulVec_mem_glImage hx)
    rwa [evalIn_mulVec_of_mem Q hγ] at this
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := mem_glImage.mp hy
    rw [evalIn_mulVec_of_mem Q hγ]; exact h x hx

/-- **$O(V)$-invariance** of the neighbour relation. -/
theorem IsNbrL.glImage {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) {M M' : Submodule (𝓞 F) (Fin n → F)}
    (h : IsNbrL Q π M M') : IsNbrL Q π (glImage γ M) (glImage γ M') :=
  ⟨by rw [relIndex_glImage]; exact h.1, by rw [relIndex_glImage]; exact h.2,
    (smul_mem_glImage_iff γ _ M' M).mpr h.3, (smul_mem_glImage_iff γ _ M M').mpr h.4,
    (isIntegral_glImage hγ).mpr h.5, (isIntegral_glImage hγ).mpr h.6⟩

theorem isNbrL_glImage_iff {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) {M M' : Submodule (𝓞 F) (Fin n → F)} :
    IsNbrL Q π (glImage γ M) (glImage γ M') ↔ IsNbrL Q π M M' := by
  refine ⟨fun h => ?_, IsNbrL.glImage hγ⟩
  have h' := h.glImage ((orthGroup Q F).inv_mem hγ)
  rwa [← glImage_mul, ← glImage_mul, inv_mul_cancel, glImage_one, glImage_one] at h'

/-- $r_{\gamma M}(\nu) = r_M(\nu)$ for $\gamma \in O(V)(F)$. -/
theorem latRepF_glImage {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) (M : Submodule (𝓞 F) (Fin n → F))
    (ν : 𝓞 F) : latRepF Q (glImage γ M) ν = latRepF Q M ν := by
  unfold latRepF
  refine Nat.card_congr
    { toFun := fun x => ⟨(γ⁻¹).val *ᵥ x.1, by
        obtain ⟨hx1, hq⟩ := x.2
        obtain ⟨y, hy, hxy⟩ := mem_glImage.mp hx1
        rw [← hxy, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
        refine ⟨hy, ?_⟩
        rw [← hq, ← hxy, evalIn_mulVec_of_mem Q hγ]⟩
      invFun := fun y => ⟨γ.val *ᵥ y.1, mulVec_mem_glImage y.2.1, by
        rw [evalIn_mulVec_of_mem Q hγ]; exact y.2.2⟩
      left_inv := fun x => by apply Subtype.ext; exact mulVec_inv_mulVec γ x.1
      right_inv := fun y => by
        apply Subtype.ext
        show (γ⁻¹).val *ᵥ (γ.val *ᵥ y.1) = y.1
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] }

/-! #### Transport to the Gram form -/

lemma intVec_eq_stdLat : (intVec : Submodule (𝓞 F) (Fin n → F)) = stdLat (𝓞 F) F n := by
  ext x
  rw [mem_stdLat, mem_intVec_iff_exists]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩

lemma natCard_res (π : 𝓞 F) : Nat.card (Res π) = nm π := by
  rw [nm, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- $Q_\gamma(x) = Q(\gamma x)$ on $F^n$. -/
lemma qv_gramZ (γ : GL (Fin n) F) (h : IsIntegral Q (latOf γ)) (x : Fin n → F) :
    qv F (gramZ Q γ h) x = Q.evalIn F (γ.val *ᵥ x) := by
  rw [qv, evalIn_eq_eval_map, gramZ_map, eval_gramFormF_col]

/-- **Neighbours of a free lattice are the images of the neighbours of $\mathcal O_F^n$ for its Gram form:** for $M = \gamma\mathcal O_F^n$
integral, $\gamma N$ is a $\pi$-neighbour of $M$ iff $N$ is a $\pi$-neighbour of $\mathcal O_F^n$ for $Q_\gamma$ (`IsNbr`) with $\pi\mathcal O_F^n \subseteq N$. -/
theorem isNbrL_latOf_iff (γ : GL (Fin n) F) (h : IsIntegral Q (latOf γ)) (N : Submodule (𝓞 F) (Fin n → F)) :
    IsNbrL Q π (latOf γ) (glImage γ N) ↔
      IsNbr F (gramZ Q γ h) π N ∧ ∀ x ∈ stdLat (𝓞 F) F n, algebraMap (𝓞 F) F π • x ∈ N := by
  have hL : latOf γ = glImage γ (stdLat (𝓞 F) F n) := by rw [latOf, intVec_eq_stdLat]
  have hint : IsIntegral Q (glImage γ N) ↔ ∀ x ∈ N, ∃ z : 𝓞 F, qv F (gramZ Q γ h) x = algebraMap (𝓞 F) F z := by
    constructor
    · intro hi x hx
      obtain ⟨z, hz⟩ := hi _ (mulVec_mem_glImage hx)
      exact ⟨z, by rw [qv_gramZ]; exact hz.symm⟩
    · intro hi y hy
      obtain ⟨x, hx, rfl⟩ := mem_glImage.mp hy
      obtain ⟨z, hz⟩ := hi x hx
      exact ⟨z, by rw [← qv_gramZ γ h]; exact hz.symm⟩
  rw [hL]
  constructor
  · intro hN
    refine ⟨⟨?_, ?_, ?_, hint.mp hN.6⟩, (smul_mem_glImage_iff γ _ _ _).mp hN.4⟩
    · have := hN.1; rwa [relIndex_glImage, ← natCard_res] at this
    · have := hN.2; rwa [relIndex_glImage, ← natCard_res] at this
    · exact (smul_mem_glImage_iff γ _ _ _).mp hN.3
  · rintro ⟨hN, hs⟩
    refine ⟨?_, ?_, (smul_mem_glImage_iff γ _ _ _).mpr hN.smul_mem, (smul_mem_glImage_iff γ _ _ _).mpr hs,
      by rw [← hL]; exact h, hint.mpr hN.integral⟩
    · rw [relIndex_glImage, ← natCard_res]; exact hN.relIndex_std
    · rw [relIndex_glImage, ← natCard_res]; exact hN.relIndex_self

/-- $r_{\gamma N}(\nu)$ for $Q$ is $r_N(\nu)$ for the Gram form $Q_\gamma$. -/
theorem latRepF_glImage_eq (γ : GL (Fin n) F) (h : IsIntegral Q (latOf γ)) (N : Submodule (𝓞 F) (Fin n → F))
    (ν : 𝓞 F) : latRepF Q (glImage γ N) ν = latRep F (gramZ Q γ h) N ν := by
  unfold latRepF latRep
  refine Nat.card_congr
    { toFun := fun x => ⟨(γ⁻¹).val *ᵥ x.1, by
        obtain ⟨hx1, hq⟩ := x.2
        obtain ⟨y, hy, hxy⟩ := mem_glImage.mp hx1
        rw [← hxy, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
        refine ⟨hy, ?_⟩
        rw [qv_gramZ, hxy, hq]⟩
      invFun := fun y => ⟨γ.val *ᵥ y.1, mulVec_mem_glImage y.2.1, by
        rw [← qv_gramZ γ h]; exact y.2.2⟩
      left_inv := fun x => by apply Subtype.ext; exact mulVec_inv_mulVec γ x.1
      right_inv := fun y => by
        apply Subtype.ext
        show (γ⁻¹).val *ᵥ (γ.val *ᵥ y.1) = y.1
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] }

/-- **The neighbours of a free lattice, as a set**: $\{M' : M' \sim_\pi \gamma\mathcal O_F^n\} = \gamma\cdot\{\pi\text{-neighbours of } \mathcal O_F^n \text{ for } Q_\gamma\}$
($\pi$ prime, $\pi \nmid \det H(Q_\gamma)$). -/
theorem setOf_isNbrL_latOf (hπ : Prime π) [Fintype (Res π)] [DecidableEq (Res π)] (γ : GL (Fin n) F)
    (h : IsIntegral Q (latOf γ)) (hdet : ¬ π ∣ (gramZ Q γ h).hessian.det) :
    {M' | IsNbrL Q π (latOf γ) M'} = glImage γ '' ((neighbors F (gramZ Q γ h) π : Finset _) : Set _) := by
  have := isMaximal_span hπ
  ext M'
  have hM' : M' = glImage γ (glImage γ⁻¹ M') := by rw [← glImage_mul, mul_inv_cancel, glImage_one]
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe]
  constructor
  · intro hN
    rw [hM', isNbrL_latOf_iff γ h] at hN
    exact ⟨_, (mem_neighbors_iff hπ hdet).mpr hN.1, hM'.symm⟩
  · rintro ⟨N, hN, rfl⟩
    rw [isNbrL_latOf_iff γ h]
    refine ⟨(mem_neighbors_iff hπ hdet).mp hN, ?_⟩
    -- `πR^n ⊆ L(v)` for every neighbour
    unfold neighbors at hN
    obtain ⟨vb, hvb, rfl⟩ := Finset.mem_image.mp hN
    rintro _ ⟨z, rfl⟩
    obtain ⟨-, h2⟩ := liftV_spec hπ hdet hvb
    unfold nbOf
    rw [← cv_smul]; exact smul_cv_mem_nbLat hπ h2 z

end LatNbr

end QuadFormsKB.Lattices.Nbr
