/-
# Square-class duality: the finite Poisson formula behind Weil's Lemma 4.5.3

**Layer:** finite abelian groups (this part); local square classes and $S$-units (later parts).

Weil (1982, §4.5, Lemma 4.5.3, pp. 104–105) writes the indicator of $H_Sk^\times$ in $I_k$ as $2^{-|S|}\sum_{\lambda}\lambda$ over
the characters $\lambda$ of $I_k/H_Sk^\times$, which he identifies, by class field theory, with the characters of the quadratic
extensions $k(\sqrt d)$, $d \in E_S$. We avoid class field theory: on the finite group $G_S = \prod_{v\in S\cup\infty}
k_v^\times/k_v^{\times2}$ the product of the local Hilbert symbols is a perfect symmetric pairing, the image $\Lambda$ of
$E_S/E_S^2$ is isotropic (Hilbert reciprocity) and $|\Lambda|^2 = |G_S|$ (Dirichlet–Chevalley, `HN.index_sq_sUnit`, and the
local square-class counts, `HN.prod_index_sq`); hence $\Lambda^\perp = \Lambda$, and
$$\mathbf 1_\Lambda(y) = |\Lambda|^{-1}\sum_{\lambda\in\Lambda}\langle\lambda, y\rangle\qquad(\texttt{sum\_pairing\_eq}),$$
which is the identity Weil uses.

**This part** (`Pairing`): for a finite commutative group $G$ with a symmetric, bimultiplicative, nondegenerate pairing
$B : G \times G \to \{\pm1\}$ and a subgroup $\Lambda$ with $B(\Lambda,\Lambda) = 1$ and $|\Lambda|^2 = |G|$:
$\sum_{x\in\Lambda}B(x,y) = |\Lambda|\cdot\mathbf 1[y\in\Lambda]$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.HasseNorm.Reciprocity

open Finset NumberField IsDedekindDomain
open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SqDual

section Pairing

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- A $\pm1$-valued function that is multiplicative on a subgroup $H$ sums to $0$ over $H$ unless it is $\equiv 1$ there. -/
lemma sum_char_subgroup (H : Subgroup G) [DecidablePred (· ∈ H)] (χ : G → ℤ)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, χ (x * y) = χ x * χ y) {x₀ : G} (hx₀ : x₀ ∈ H) (hχ : χ x₀ = -1) :
    ∑ x ∈ univ.filter (· ∈ H), χ x = 0 := by
  set A := univ.filter (· ∈ H)
  have hbij : ∑ x ∈ A, χ (x₀ * x) = ∑ x ∈ A, χ x := by
    refine Finset.sum_bij (fun x _ => x₀ * x) (fun x hx => ?_) (fun a _ b _ h => mul_left_cancel h)
      (fun y hy => ⟨x₀⁻¹ * y, ?_, by group⟩) (fun _ _ => rfl)
    · simp only [A, mem_filter, mem_univ, true_and] at hx ⊢; exact H.mul_mem hx₀ hx
    · simp only [A, mem_filter, mem_univ, true_and] at hy ⊢; exact H.mul_mem (H.inv_mem hx₀) hy
  have : ∑ x ∈ A, χ (x₀ * x) = -∑ x ∈ A, χ x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [A, mem_filter, mem_univ, true_and] at hx
    rw [hmul x₀ hx₀ x hx, hχ]; ring
  linarith

variable (B : G → G → ℤ)

/-- **The finite Poisson formula for a Lagrangian subgroup.** Let $B$ be a symmetric pairing $G \times G \to \{\pm1\}$, multiplicative
in the first variable, nondegenerate ($y \ne 1 \Rightarrow \exists x,\ B(x,y) = -1$), and let $\Lambda \le G$ be isotropic
($B(\Lambda,\Lambda) = 1$) with $|\Lambda|^2 = |G|$. Then for every $y \in G$,
$$\sum_{x\in\Lambda}B(x,y) = \begin{cases}|\Lambda| & y\in\Lambda,\\ 0 & y\notin\Lambda.\end{cases}$$
*Proof.* For fixed $y$, $x \mapsto B(x,y)$ is a character of $\Lambda$, so the sum is $|\Lambda|\mathbf 1[y\in\Lambda^\perp]$; double
counting with nondegeneracy gives $|\Lambda|\,|\Lambda^\perp| = |G|$, so $|\Lambda^\perp| = |\Lambda|$, and $\Lambda \subseteq \Lambda^\perp$. -/
@[kb "weil1982" "§4.5, Lemma 4.5.3, p. 104 (characters of I_k/H_S k^*; here by a perfect pairing, no CFT)"]
theorem sum_pairing_eq (hB : ∀ x y, B x y = 1 ∨ B x y = -1) (hmul : ∀ x x' y, B (x * x') y = B x y * B x' y)
    (hsymm : ∀ x y, B x y = B y x) (hnd : ∀ y, y ≠ 1 → ∃ x, B x y = -1)
    (Λ : Subgroup G) [DecidablePred (· ∈ Λ)] (hiso : ∀ x ∈ Λ, ∀ y ∈ Λ, B x y = 1)
    (hcard : (univ.filter (· ∈ Λ)).card * (univ.filter (· ∈ Λ)).card = Fintype.card G) (y : G) :
    ∑ x ∈ univ.filter (· ∈ Λ), B x y = if y ∈ Λ then ((univ.filter (· ∈ Λ)).card : ℤ) else 0 := by
  classical
  set A := univ.filter (· ∈ Λ)
  -- the orthogonal complement
  set P : G → Prop := fun y => ∀ x ∈ Λ, B x y = 1
  have hsumy : ∀ y, ∑ x ∈ A, B x y = if P y then (A.card : ℤ) else 0 := by
    intro y
    split_ifs with hy
    · rw [Finset.sum_congr rfl fun x hx => hy x (by simpa [A] using hx)]; simp
    · simp only [P, not_forall] at hy
      obtain ⟨x₀, hx₀, hne⟩ := hy
      have hx₀' : B x₀ y = -1 := (hB x₀ y).resolve_left hne
      exact sum_char_subgroup Λ (fun x => B x y) (fun x _ x' _ => hmul x x' y) hx₀ hx₀'
  -- the full sums over y
  have hsumx : ∀ x, ∑ y, B x y = if x = 1 then (Fintype.card G : ℤ) else 0 := by
    intro x
    split_ifs with hx
    · subst hx
      have h1 : ∀ y, B 1 y = 1 := fun y => by
        have := hmul 1 1 y
        rw [mul_one] at this
        rcases hB 1 y with h | h <;> [exact h; (rw [h] at this; norm_num at this)]
      simp [h1]
    · obtain ⟨y₀, hy₀⟩ := hnd x hx
      have := sum_char_subgroup (⊤ : Subgroup G) (fun y => B x y)
        (fun a _ b _ => by rw [hsymm x, hsymm x, hsymm x, hmul]) (Subgroup.mem_top y₀)
        (by rw [hsymm]; exact hy₀)
      simpa using this
  -- double counting
  have hdc : ∑ y, ∑ x ∈ A, B x y = (Fintype.card G : ℤ) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun x _ => hsumx x]
    rw [Finset.sum_ite_eq' A 1]
    simp [A, Λ.one_mem]
  have hperp : ((univ.filter P).card : ℤ) * A.card = Fintype.card G := by
    rw [← hdc, Finset.sum_congr rfl fun y _ => hsumy y, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
  have hAsub : A ⊆ univ.filter P := by
    intro x hx
    simp only [A, mem_filter, mem_univ, true_and] at hx ⊢
    intro x' hx'
    exact hiso x' hx' x hx
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨1, by simp [A, Λ.one_mem]⟩
  have hcardP : (univ.filter P).card = A.card := by
    have h1 : ((univ.filter P).card : ℤ) * A.card = A.card * A.card := by rw [hperp]; exact_mod_cast hcard.symm
    have := mul_right_cancel₀ (by exact_mod_cast hApos.ne' : (A.card : ℤ) ≠ 0) h1
    exact_mod_cast this
  have hAeq : A = univ.filter P := Finset.eq_of_subset_of_card_le hAsub hcardP.le
  have hPy : P y ↔ y ∈ Λ := by
    have : y ∈ univ.filter P ↔ y ∈ A := by rw [hAeq]
    simpa [A] using this
  rw [hsumy y]
  simp only [hPy]

end Pairing

/-! ### Square classes of a field and the Hilbert pairing on them -/

section SqCl

variable (K : Type*) [Field K]

/-- **The square classes** $K^\times/K^{\times2}$ of a field. -/
abbrev SqCl : Type _ := Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range

lemma hilbertSymbol_mul_sq_right (a b d : K) (hd : d ≠ 0) :
    hilbertSymbol K a (b * d ^ 2) = hilbertSymbol K a b := by
  rw [hilbertSymbol_comm, HN.hilbertSymbol_mul_sq_left K b a d hd, hilbertSymbol_comm]

/-- **The Hilbert symbol on square classes:** $([a],[b]) \mapsto (a,b)_K$ (well defined since $(ad^2, b) = (a, b)$). -/
noncomputable def hilbCl : SqCl K → SqCl K → ℤ :=
  Quotient.lift₂ (fun a b : Kˣ => hilbertSymbol K (a : K) (b : K)) (by
    rintro a b a' b' ha hb
    obtain ⟨d, hd⟩ := QuotientGroup.leftRel_apply.mp ha
    obtain ⟨e, he⟩ := QuotientGroup.leftRel_apply.mp hb
    have ha' : (a' : K) = a * (d : K) ^ 2 := by
      have := congrArg Units.val hd
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul] at this
      rw [this, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    have hb' : (b' : K) = b * (e : K) ^ 2 := by
      have := congrArg Units.val he
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul] at this
      rw [this, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    show hilbertSymbol K (a : K) (b : K) = hilbertSymbol K (a' : K) (b' : K)
    rw [ha', hb', HN.hilbertSymbol_mul_sq_left K _ _ _ d.ne_zero, hilbertSymbol_mul_sq_right K _ _ _ e.ne_zero])

@[simp] lemma hilbCl_mk (a b : Kˣ) :
    hilbCl K (QuotientGroup.mk a) (QuotientGroup.mk b) = hilbertSymbol K (a : K) (b : K) := rfl

lemma hilbCl_pm (x y : SqCl K) : hilbCl K x y = 1 ∨ hilbCl K x y = -1 := by
  induction x using QuotientGroup.induction_on
  induction y using QuotientGroup.induction_on
  exact HN.hilbertSymbol_eq_one_or K _ _

lemma hilbCl_symm (x y : SqCl K) : hilbCl K x y = hilbCl K y x := by
  induction x using QuotientGroup.induction_on
  induction y using QuotientGroup.induction_on
  exact hilbertSymbol_comm K _ _

/-- $[a] = 1$ in $K^\times/K^{\times2}$ iff $a$ is a square. -/
lemma mk_eq_one_iff_isSquare (a : Kˣ) : (QuotientGroup.mk a : SqCl K) = 1 ↔ IsSquare (a : K) := by
  rw [QuotientGroup.eq_one_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨d, hd⟩; exact ⟨d, by rw [← hd]; simp [sq]⟩
  · rintro ⟨d, hd⟩
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd
    exact ⟨Units.mk0 d hd0, Units.ext (by simp [hd, sq])⟩

end SqCl

/-! ### The local pairings at the places of a number field -/

section Local

variable {F : Type} [Field F] [NumberField F]

lemma hilbCl_mul_fin (v : HeightOneSpectrum (𝓞 F)) (x x' y : SqCl (v.adicCompletion F)) :
    hilbCl _ (x * x') y = hilbCl _ x y * hilbCl _ x' y := by
  induction x using QuotientGroup.induction_on
  induction x' using QuotientGroup.induction_on
  induction y using QuotientGroup.induction_on
  rw [← QuotientGroup.mk_mul, hilbCl_mk, hilbCl_mk, hilbCl_mk, Units.val_mul]
  exact HN.hilbertSymbol_mul_left_finite_nf v _ _ _ (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _)

lemma hilbCl_mul_inf (w : InfinitePlace F) (x x' y : SqCl w.Completion) :
    hilbCl _ (x * x') y = hilbCl _ x y * hilbCl _ x' y := by
  induction x using QuotientGroup.induction_on
  induction x' using QuotientGroup.induction_on
  induction y using QuotientGroup.induction_on
  rw [← QuotientGroup.mk_mul, hilbCl_mk, hilbCl_mk, hilbCl_mk, Units.val_mul]
  exact NFLocal.hilbertSymbol_mul_left_infinite_nf w _ _ _ (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _)

attribute [local instance] HN.compAlgebra in
/-- **Local nondegeneracy at a finite place** (every place, dyadic included): if $c \in F_v^\times$ is not a square, then
$(x, c)_v = -1$ for some $x$. *Proof:* $c = a_0d^2$ with $a_0 \in F$; the kernel of $(a_0,\cdot)_v$ is the norm group of
$F_v\otimes_F F(\sqrt{a_0})$ (`HN.mem_range_norm_iff`), of index $2$ (`HN.index_norm_eq_two`). -/
@[kb "serre1973" "Ch. III §1.1, Prop. 1 and §2.2, Thm. 2 (nondegeneracy) [unverified]; omeara1963 §63B, 63:13, p. 166; cassels1978 Ch. 3, Lemma 2.1 (iii), p. 42"]
theorem hilbCl_nondeg_fin (v : HeightOneSpectrum (𝓞 F)) (y : SqCl (v.adicCompletion F)) (hy : y ≠ 1) :
    ∃ x, hilbCl _ x y = -1 := by
  induction y using QuotientGroup.induction_on with
  | H c =>
  have hc : ¬ IsSquare (c : v.adicCompletion F) := fun h => hy ((mk_eq_one_iff_isSquare _ c).mpr h)
  obtain ⟨a₀, ha₀, d, hd, hcd⟩ := HN.exists_global_mul_sq v (c : v.adicCompletion F) c.ne_zero
  have hv : ¬ IsSquare (algebraMap F (v.adicCompletion F) a₀) := fun h => hc (hcd ▸ h.mul ⟨d, sq d⟩)
  have hd' : ¬ IsSquare a₀ := fun h => hv (h.map _)
  obtain ⟨L, _, _, _, s, hs, hspan⟩ := QuadFormsKB.Lam.exists_quadExt a₀ hd'
  obtain ⟨hQ, -, -, -⟩ := HN.quadData a₀ hd' s hs hspan
  obtain ⟨w, rfl⟩ := HN.exists_over (L := L) v
  have hidx := HN.index_norm_eq_two a₀ hd' s hs hspan w hv
  have hne : (Units.map (Algebra.norm (HeightOneSpectrum.adicCompletion F (HN.under (F := F) w)) :
      (HeightOneSpectrum.adicCompletion F (HN.under (F := F) w)) ⊗[F] L →*
        HeightOneSpectrum.adicCompletion F (HN.under (F := F) w))).range ≠ ⊤ := by
    intro h; rw [h, Subgroup.index_top] at hidx; norm_num at hidx
  obtain ⟨x, hx⟩ : ∃ x, x ∉ (Units.map (Algebra.norm (HeightOneSpectrum.adicCompletion F (HN.under (F := F) w)) :
      (HeightOneSpectrum.adicCompletion F (HN.under (F := F) w)) ⊗[F] L →*
        HeightOneSpectrum.adicCompletion F (HN.under (F := F) w))).range := by
    by_contra h; push Not at h; exact hne (eq_top_iff.mpr fun x _ => h x)
  have h1 := (HN.mem_range_norm_iff a₀ hd' s hs hspan w x).not.mp hx
  refine ⟨QuotientGroup.mk x, ?_⟩
  rw [hilbCl_mk, hilbertSymbol_comm, hcd, HN.hilbertSymbol_mul_sq_left _ _ _ _ hd]
  exact (HN.hilbertSymbol_eq_one_or _ _ _).resolve_left h1

/-- **Local nondegeneracy at an infinite place:** at a real place a non-square $c$ is negative and $(c,c)_w = -1$; at a complex
place every class is trivial. -/
@[kb "omeara1963" "§63B, 63:13, p. 166; cassels1978 Ch. 3, Lemma 2.1 (iii), p. 42"]
theorem hilbCl_nondeg_inf (w : InfinitePlace F) (y : SqCl w.Completion) (hy : y ≠ 1) :
    ∃ x, hilbCl _ x y = -1 := by
  induction y using QuotientGroup.induction_on with
  | H c =>
  have hc : ¬ IsSquare (c : w.Completion) := fun h => hy ((mk_eq_one_iff_isSquare _ c).mpr h)
  rcases w.isReal_or_isComplex with hw | hw
  · set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have hec : e (c : w.Completion) < 0 := by
      by_contra h
      push Not at h
      apply hc
      obtain ⟨r, hr⟩ : ∃ r : ℝ, e (c : w.Completion) = r * r :=
        ⟨Real.sqrt (e c), (Real.mul_self_sqrt h).symm⟩
      exact ⟨e.symm r, by apply e.injective; rw [map_mul, RingEquiv.apply_symm_apply, hr]⟩
    refine ⟨QuotientGroup.mk c, ?_⟩
    rw [hilbCl_mk, HN.hilbertSymbol_ringEquiv e]
    exact (hilbertSymbol_real _ _ hec.ne hec.ne).mpr ⟨hec, hec⟩
  · exfalso
    apply hc
    set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    obtain ⟨z, hz⟩ := IsAlgClosed.isSquare (e (c : w.Completion))
    exact ⟨e.symm z, by apply e.injective; rw [map_mul, RingEquiv.apply_symm_apply, hz]⟩

end Local

/-! ### The global group $G_S$ and its pairing -/

section Global

variable {F : Type} [Field F] [NumberField F]

instance finite_sqCl_fin (v : HeightOneSpectrum (𝓞 F)) : Finite (SqCl (v.adicCompletion F)) := by
  have h := HN.index_sq_completion v
  have hne : (powMonoidHom 2 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range.index ≠ 0 := by
    rw [h]
    refine mul_ne_zero (by norm_num) (pow_ne_zero _ ?_)
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have : (powMonoidHom 2 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range.FiniteIndex := ⟨hne⟩
  exact Subgroup.finite_quotient_of_finiteIndex

instance finite_sqCl_inf (w : InfinitePlace F) : Finite (SqCl w.Completion) := by
  have h := HN.index_sq_infinite w
  have : (powMonoidHom 2 : w.Completionˣ →* w.Completionˣ).range.FiniteIndex :=
    ⟨by rw [h]; split_ifs <;> norm_num⟩
  exact Subgroup.finite_quotient_of_finiteIndex

variable (F) in
/-- **The group $G_S = \prod_{v\in S}F_v^\times/F_v^{\times2}\times\prod_{w\mid\infty}F_w^\times/F_w^{\times2}$** ($S$ a finite set of
finite places). Weil's $I_k/H_S$ restricted to the places in $S \cup \infty$ (p. 104). -/
abbrev GS (S : Finset (HeightOneSpectrum (𝓞 F))) : Type :=
  ((v : S) → SqCl (v.1.adicCompletion F)) × ((w : InfinitePlace F) → SqCl w.Completion)

noncomputable instance (S : Finset (HeightOneSpectrum (𝓞 F))) : Fintype (GS F S) := Fintype.ofFinite _

instance (S : Finset (HeightOneSpectrum (𝓞 F))) : CommGroup (GS F S) := inferInstance

/-- **$|G_S| = 4^{|S| + r_\infty}$** for $S$ containing the dyadic places (`HN.prod_index_sq`: $[F_v^\times:F_v^{\times2}] =
4N\mathfrak p^{\operatorname{ord}_v2}$, $2$ or $1$ at real or complex places, and $\prod_{v\mid2}N\mathfrak p^{\operatorname{ord}_v2} = 2^{[F:\mathbb Q]}$). -/
theorem card_GS (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S) :
    Fintype.card (GS F S) = 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_prod, Nat.card_pi, Nat.card_pi, ← HN.prod_index_sq S hS]
  refine congrArg₂ (· * ·) ?_ rfl
  rw [← Finset.prod_coe_sort S]
  rfl

/-- **The localization map** $F^\times \to G_S$, $\rho \mapsto ([\rho]_v)_{v\in S\cup\infty}$. -/
noncomputable def locMap (S : Finset (HeightOneSpectrum (𝓞 F))) : Fˣ →* GS F S :=
  MonoidHom.prod
    (MonoidHom.pi fun v : S => (QuotientGroup.mk' _).comp (Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom))
    (MonoidHom.pi fun w : InfinitePlace F =>
      (QuotientGroup.mk' _).comp (Units.map (algebraMap F w.Completion).toMonoidHom))

/-- **The product pairing** $\langle x, y\rangle_S = \prod_{v\in S\cup\infty}(x_v, y_v)_v$ on $G_S$. -/
noncomputable def BS (S : Finset (HeightOneSpectrum (𝓞 F))) (x y : GS F S) : ℤ :=
  (∏ v : S, hilbCl _ (x.1 v) (y.1 v)) * ∏ w : InfinitePlace F, hilbCl _ (x.2 w) (y.2 w)

lemma prod_pm {ι : Type*} (s : Finset ι) (f : ι → ℤ) (hf : ∀ i, f i = 1 ∨ f i = -1) :
    (∏ i ∈ s, f i) = 1 ∨ (∏ i ∈ s, f i) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    rcases hf a with h | h <;> rcases ih with h' | h' <;> simp [h, h']

lemma BS_pm (S : Finset (HeightOneSpectrum (𝓞 F))) (x y : GS F S) : BS S x y = 1 ∨ BS S x y = -1 := by
  have h1 := prod_pm Finset.univ (fun v : S => hilbCl _ (x.1 v) (y.1 v)) fun v => hilbCl_pm _ _ _
  have h2 := prod_pm Finset.univ (fun w : InfinitePlace F => hilbCl _ (x.2 w) (y.2 w)) fun w => hilbCl_pm _ _ _
  unfold BS
  rcases h1 with h | h <;> rcases h2 with h' | h' <;> rw [h, h'] <;> norm_num

lemma BS_mul (S : Finset (HeightOneSpectrum (𝓞 F))) (x x' y : GS F S) :
    BS S (x * x') y = BS S x y * BS S x' y := by
  unfold BS
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
  rw [Finset.prod_congr rfl fun v _ => hilbCl_mul_fin v.1 _ _ _,
    Finset.prod_congr rfl fun w _ => hilbCl_mul_inf w _ _ _, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

lemma BS_symm (S : Finset (HeightOneSpectrum (𝓞 F))) (x y : GS F S) : BS S x y = BS S y x := by
  unfold BS
  rw [Finset.prod_congr rfl fun v _ => hilbCl_symm _ (x.1 v) (y.1 v),
    Finset.prod_congr rfl fun w _ => hilbCl_symm _ (x.2 w) (y.2 w)]

lemma BS_mul_right' (S : Finset (HeightOneSpectrum (𝓞 F))) (x y y' : GS F S) :
    BS S x (y * y') = BS S x y * BS S x y' := by
  rw [BS_symm, BS_mul, BS_symm S y, BS_symm S y']

lemma hilbCl_one_left (K : Type*) [Field K] (y : SqCl K) : hilbCl K 1 y = 1 := by
  induction y using QuotientGroup.induction_on
  rw [← QuotientGroup.mk_one, hilbCl_mk]
  unfold hilbertSymbol
  split_ifs with h
  · rfl
  · exact absurd ⟨1, 0, 1, by simp, by simp⟩ h

/-- **$\langle\,,\rangle_S$ is nondegenerate** (product of the local nondegeneracies). -/
theorem BS_nondeg (S : Finset (HeightOneSpectrum (𝓞 F))) (y : GS F S) (hy : y ≠ 1) :
    ∃ x, BS S x y = -1 := by
  classical
  by_cases h1 : y.1 = 1
  · have h2 : y.2 ≠ 1 := fun h => hy (Prod.ext h1 h)
    obtain ⟨w, hw⟩ : ∃ w, y.2 w ≠ 1 := by
      by_contra h; push Not at h; exact h2 (funext h)
    obtain ⟨c, hc⟩ := hilbCl_nondeg_inf w (y.2 w) hw
    refine ⟨(1, Pi.mulSingle w c), ?_⟩
    unfold BS
    have e1 : ∏ v : S, hilbCl _ ((1 : GS F S).1 v) (y.1 v) = 1 :=
      Finset.prod_eq_one fun v _ => hilbCl_one_left _ _
    have e2 : ∏ w' : InfinitePlace F, hilbCl _ (Pi.mulSingle (M := fun w' : InfinitePlace F => SqCl w'.Completion)
        w c w') (y.2 w') = hilbCl _ c (y.2 w) := by
      rw [Finset.prod_eq_single w (fun w' _ hw' => by rw [Pi.mulSingle_eq_of_ne hw', hilbCl_one_left])
        (by simp), Pi.mulSingle_eq_same]
    simp only [Pi.one_apply]
    rw [Finset.prod_eq_one (fun v _ => hilbCl_one_left _ _), e2, one_mul, hc]
  · obtain ⟨v, hv⟩ : ∃ v, y.1 v ≠ 1 := by
      by_contra h; push Not at h; exact h1 (funext h)
    obtain ⟨c, hc⟩ := hilbCl_nondeg_fin v.1 (y.1 v) hv
    refine ⟨(Pi.mulSingle v c, 1), ?_⟩
    unfold BS
    have e1 : ∏ w : InfinitePlace F, hilbCl _ ((1 : GS F S).2 w) (y.2 w) = 1 :=
      Finset.prod_eq_one fun w _ => hilbCl_one_left _ _
    have e2 : ∏ v' : S, hilbCl _ (Pi.mulSingle (M := fun v' : S => SqCl (v'.1.adicCompletion F))
        v c v') (y.1 v') = hilbCl _ c (y.1 v) := by
      rw [Finset.prod_eq_single v (fun v' _ hv' => by rw [Pi.mulSingle_eq_of_ne hv', hilbCl_one_left])
        (by simp), Pi.mulSingle_eq_same]
    simp only [Pi.one_apply]
    rw [Finset.prod_eq_one (fun w _ => hilbCl_one_left _ _), e2, mul_one, hc]

lemma BS_locMap (S : Finset (HeightOneSpectrum (𝓞 F))) (a b : Fˣ) :
    BS S (locMap S a) (locMap S b) =
      (∏ v : S, (NFPlace.finite v.1).hilbert (a : F) (b : F)) *
        ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (a : F) (b : F) := by
  rfl

end Global

/-! ### Isotropy of the $S$-units (Hilbert reciprocity) -/

section Iso

variable {F : Type} [Field F] [NumberField F]

/-- **Two units at a non-dyadic place have Hilbert symbol $1$** (Serre III §1.2, Thm. 1, over $F_v$): $\langle a, b, -1\rangle$ is
isotropic over $F_v$ (`NFLocal.isotropic_diag_units_nf`). -/
@[kb "omeara1963" "§63B, 63:12, p. 166"]
theorem hilbert_units_nondyadic (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (a b : F)
    (ha : v.valuation F a = 1) (hb : v.valuation F b = 1) : (NFPlace.finite v).hilbert a b = 1 := by
  have hm1 : v.valuation F (-1 : F) = 1 := by rw [Valuation.map_neg, map_one]
  obtain ⟨x, hx0, hx⟩ := NFLocal.isotropic_diag_units_nf v h2 3 le_rfl ![a, b, -1] (by
    intro i; fin_cases i <;> simp [ha, hb, hm1])
  have hev : QuadForm.evalIn (v.adicCompletion F) (QuadForm.diag ![a, b, -1]) x =
      algebraMap F _ a * x 0 ^ 2 + algebraMap F _ b * x 1 ^ 2 - x 2 ^ 2 := by
    simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three, Matrix.diagonal]
    ring
  rw [hev] at hx
  rw [NFPlace.hilbert]
  unfold hilbertSymbol
  split_ifs with h
  · rfl
  · exfalso; apply h
    refine ⟨x 0, x 1, x 2, ?_, by linear_combination -hx⟩
    intro h0
    apply hx0
    simp only [Prod.mk_eq_zero] at h0
    funext i; fin_cases i <;> simp [h0.1, h0.2.1, h0.2.2]

lemma prod_pm_eq_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℤ) (hf : ∀ i, f i = 1 ∨ f i = -1) :
    ∏ i, f i = (-1) ^ (Finset.univ.filter fun i => f i = -1).card := by
  have : ∀ i, f i = if f i = -1 then -1 else 1 := fun i => by
    rcases hf i with h | h <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_ite]
  simp

/-- **Isotropy of $E_S$** (Hilbert reciprocity, `HN.hilbert_product_formula_nf`): for $S$-units $a, b$ ($S \ni$ the dyadic
places), $\langle[a],[b]\rangle_S = \prod_{v\in S\cup\infty}(a,b)_v = 1$, since $(a,b)_v = 1$ at the other places. -/
theorem BS_locMap_sUnit (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S) {a b : Fˣ} (ha : a ∈ HN.SUnit S)
    (hb : b ∈ HN.SUnit S) : BS S (locMap S a) (locMap S b) = 1 := by
  classical
  rw [BS_locMap]
  set hf : S → ℤ := fun v => (NFPlace.finite v.1).hilbert (a : F) (b : F)
  set hi : InfinitePlace F → ℤ := fun w => (NFPlace.infinite w).hilbert (a : F) (b : F)
  have hpm : ∀ v : NFPlace F, v.hilbert (a : F) (b : F) = 1 ∨ v.hilbert (a : F) (b : F) = -1 := by
    intro v; cases v <;> exact HN.hilbertSymbol_eq_one_or _ _ _
  rw [prod_pm_eq_pow hf fun v => hpm _, prod_pm_eq_pow hi fun w => hpm _, ← pow_add]
  obtain ⟨hfin, heven⟩ := HN.hilbert_product_formula_nf (a : F) (b : F) a.ne_zero b.ne_zero
  have hout : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → (NFPlace.finite v).hilbert (a : F) (b : F) = 1 := by
    intro v hv
    exact hilbert_units_nondyadic v (fun h => hv (hS v h)) _ _ (ha v hv) (hb v hv)
  set A := Finset.univ.filter fun v : S => hf v = -1
  set B := Finset.univ.filter fun w : InfinitePlace F => hi w = -1
  have hE : {v : NFPlace F | v.hilbert (a : F) (b : F) = -1} =
      (fun v : S => NFPlace.finite v.1) '' (A : Set S) ∪ NFPlace.infinite '' (B : Set (InfinitePlace F)) := by
    ext v
    cases v with
    | infinite w => simp [B, hi]
    | finite v =>
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and,
        reduceCtorEq, and_false, exists_false, or_false, A, hf]
      constructor
      · intro h
        by_cases hv : v ∈ S
        · exact ⟨⟨v, hv⟩, h, rfl⟩
        · rw [hout v hv] at h; norm_num at h
      · rintro ⟨v', h, hv'⟩
        cases hv'
        exact h
  have hinj1 : Function.Injective fun v : S => (NFPlace.finite v.1 : NFPlace F) := by
    intro x y h
    exact Subtype.ext (NFPlace.finite.inj h)
  have hinj2 : Function.Injective (NFPlace.infinite (F := F)) := fun x y h => by cases h; rfl
  have hdisj : Disjoint ((fun v : S => NFPlace.finite v.1) '' (A : Set S))
      (NFPlace.infinite '' (B : Set (InfinitePlace F))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, -, rfl⟩ ⟨w, -, h⟩
    cases h
  rw [hE, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ hinj1, Set.ncard_image_of_injective _ hinj2,
    Set.ncard_coe_finset, Set.ncard_coe_finset] at heven
  exact heven.neg_one_pow

end Iso

/-! ### The Lagrangian $\Lambda_S$ = image of the $S$-units -/

section Lagrangian

variable {F : Type} [Field F] [NumberField F]

/-- **The kernel condition** (Weil 1982, Lemma 4.5.3, p. 104, "$k^\times \cap H_S = k^{\times2}$", restricted to $S$-units): an
$S$-unit which is a square at every $v \in S$ and at every infinite place is a square in $F$. It holds for every $S$ containing
a suitable finite set (`exists_sqKernelCond`). -/
def SqKernelCond (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ u ∈ HN.SUnit S, locMap S u = 1 → IsSquare (u : F)

/-- $\Lambda_S$: the image of the $S$-units in $G_S$. -/
noncomputable abbrev LamS (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GS F S) := (HN.SUnit S).map (locMap S)

lemma valuation_eq_one_of_sq {v : HeightOneSpectrum (𝓞 F)} {y : F} (h : v.valuation F (y * y) = 1) :
    v.valuation F y = 1 := by
  rw [map_mul] at h
  have hy : v.valuation F y ≠ 0 := by intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
  rcases lt_trichotomy (v.valuation F y) 1 with hl | he | hg
  · exfalso
    have : v.valuation F y * v.valuation F y < 1 := mul_lt_one_of_lt_of_le hl hl.le
    rw [h] at this; exact lt_irrefl _ this
  · exact he
  · exfalso
    have : 1 < v.valuation F y * v.valuation F y := one_lt_mul hg.le hg
    rw [h] at this; exact lt_irrefl _ this

lemma card_map_eq_index {G H : Type*} [CommGroup G] [CommGroup H] (f : G →* H) (K : Subgroup G) :
    Nat.card (K.map f) = (f.comp K.subtype).ker.index := by
  rw [Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype]

lemma sqCl_sq (K : Type*) [Field K] (g : SqCl K) : g ^ 2 = 1 := by
  induction g using QuotientGroup.induction_on with
  | H a => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact ⟨a, rfl⟩

lemma GS_sq (S : Finset (HeightOneSpectrum (𝓞 F))) (x : GS F S) : x ^ 2 = 1 :=
  Prod.ext (funext fun v => sqCl_sq _ (x.1 v)) (funext fun w => sqCl_sq _ (x.2 w))

/-- **$|\Lambda_S| = 2^{|S| + r_\infty}$** under the kernel condition: $\Lambda_S \cong E_S/E_S^2$ and $[E_S : E_S^2] =
2^{\operatorname{rk}E_S + 1} = 2^{|S| + r_\infty}$ (Dirichlet–Chevalley, `HN.index_sq_sUnit`; Weil p. 105). -/
@[kb "weil1982" "§4.5, proof of Lemma 4.5.3, p. 105 ([E_S : E_S^2], Dirichlet–Chevalley)"]
theorem card_LamS (S : Finset (HeightOneSpectrum (𝓞 F))) (hker : SqKernelCond S) :
    Nat.card (LamS S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  set φ : HN.SUnit S →* GS F S := (locMap S).comp (HN.SUnit S).subtype
  have hker' : φ.ker = (powMonoidHom 2 : HN.SUnit S →* HN.SUnit S).range := by
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.mem_range, powMonoidHom_apply]
    constructor
    · intro hu
      obtain ⟨y, hy⟩ := hker u u.2 hu
      have hy0 : y ≠ 0 := by rintro rfl; simp at hy
      have hyS : Units.mk0 y hy0 ∈ HN.SUnit S := by
        intro v hv
        have := u.2 v hv
        rw [show ((u : Fˣ) : F) = y * y from hy] at this
        exact valuation_eq_one_of_sq this
      refine ⟨⟨Units.mk0 y hy0, hyS⟩, Subtype.ext (Units.ext ?_)⟩
      simp [sq, hy]
    · rintro ⟨y, rfl⟩
      rw [map_pow]
      exact GS_sq S _
  have h1 : Nat.card (LamS S) = φ.ker.index := by
    have := card_map_eq_index (G := Fˣ) (H := GS F S) (locMap S) (HN.SUnit S)
    exact this
  rw [h1, hker', show (powMonoidHom 2 : HN.SUnit S →* HN.SUnit S).range.index =
    (nsmulAddMonoidHom (α := Additive (HN.SUnit S)) 2).range.index by rw [← Subgroup.index_toAddSubgroup]; congr 1,
    HN.index_sq_sUnit, Units.rank]
  have : 1 ≤ Fintype.card (InfinitePlace F) := Fintype.card_pos
  congr 1; omega

lemma card_filter_LamS (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidablePred (· ∈ LamS S)] (hker : SqKernelCond S) :
    (Finset.univ.filter (· ∈ LamS S)).card = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  rw [← card_LamS S hker, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **The finite Poisson formula for $\Lambda_S$** (Weil 1982, Lemma 4.5.3 and p. 106, "$\Omega_S$ can also be defined as the
subset where $\lambda(F(x)) = 1$ for every $\lambda \in \gamma(S)$"): for $S \supseteq$ dyadic places with the kernel condition and
$y \in G_S$, $\sum_{x\in\Lambda_S}\langle x, y\rangle_S = |\Lambda_S|\cdot\mathbf 1[y \in \Lambda_S]$, $|\Lambda_S| = 2^{|S| + r_\infty}$. -/
@[kb "weil1982" "§4.5, Lemma 4.5.3, pp. 104–105, and p. 106 (Ω_S via the characters of I_k/H_S k^*)"]
theorem sum_LamS_BS (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S) (hker : SqKernelCond S)
    [DecidablePred (· ∈ LamS S)] (y : GS F S) :
    ∑ x ∈ Finset.univ.filter (· ∈ LamS S), BS S x y =
      if y ∈ LamS S then (2 : ℤ) ^ (S.card + Fintype.card (InfinitePlace F)) else 0 := by
  classical
  have h := sum_pairing_eq (BS S) (BS_pm S) (BS_mul S) (BS_symm S) (BS_nondeg S) (LamS S)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact BS_locMap_sUnit S hS ha hb)
    (by rw [card_filter_LamS S hker, card_GS S hS, ← pow_add, ← two_mul, pow_mul]; norm_num) y
  rw [h, card_filter_LamS S hker]
  push_cast; rfl

noncomputable instance (S : Finset (HeightOneSpectrum (𝓞 F))) : Fintype (LamS S) := Fintype.ofFinite _

lemma GS_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) (g h : GS F S) : g * (g * h) = h := by
  rw [← mul_assoc, ← sq, GS_sq]; exact one_mul (M := GS F S) h

/-- **The Poisson formula for translates of $\Lambda_S$** (Weil 1982, p. 106, $Z_S = 2^{-|S|}\sum_\lambda\int\lambda(F(x))\ldots$ in
finite form): for any $\alpha : G_S \to \mathbb R$ and $g \in G_S$,
$$\sum_{\lambda\in\Lambda_S}\alpha(g\lambda) = |\Lambda_S|^{-1}\sum_{\lambda\in\Lambda_S}\langle\lambda, g\rangle_S\,\hat\alpha(\lambda),\qquad
\hat\alpha(\lambda) = \sum_{h\in G_S}\alpha(h)\langle\lambda, h\rangle_S.$$ -/
@[kb "weil1982" "§4.5, p. 106 (Z_S(s) = 2^{-|S|} Σ_{λ∈γ(S)} ∫|F|^s λ(F(x)) Φ d'x, finite form)"]
theorem sum_LamS_translate (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S) (hker : SqKernelCond S)
    (α : GS F S → ℝ) (g : GS F S) :
    ∑ d : LamS S, α (g * d) = (Fintype.card (LamS S) : ℝ)⁻¹ *
      ∑ d : LamS S, (BS S d g : ℝ) * ∑ h, α h * (BS S d h : ℝ) := by
  classical
  have hcardpos : (0 : ℝ) < Fintype.card (LamS S) := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card (LamS S) : ℤ) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
    rw [← Nat.card_eq_fintype_card, card_LamS S hker]; push_cast; rfl
  -- the inner character sums
  have hchar : ∀ h : GS F S, ∑ d : LamS S, (BS S d (g * h) : ℝ) =
      if g * h ∈ LamS S then (Fintype.card (LamS S) : ℝ) else 0 := by
    intro h
    have h1 := sum_LamS_BS S hS hker (g * h)
    have h2 : ∑ d : LamS S, (BS S d (g * h) : ℝ) =
        ((∑ x ∈ univ.filter (· ∈ LamS S), BS S x (g * h) : ℤ) : ℝ) := by
      rw [Int.cast_sum, Finset.sum_subtype (p := (· ∈ LamS S)) (univ.filter (· ∈ LamS S)) (fun x => by simp)
        (fun x => (BS S x (g * h) : ℝ))]
    rw [h2, h1]
    split_ifs
    · rw [← hc]; push_cast; rfl
    · simp
  have hstep1 : ∑ d : LamS S, α (g * d) = ∑ h, α h * (if g * h ∈ LamS S then 1 else 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun d _ => g * d.1) (fun d _ => ?_) (fun a _ b _ hab => ?_) (fun b hb => ?_)
      (fun _ _ => rfl)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [GS_mul_self]; exact d.2
    · exact Subtype.ext (mul_left_cancel hab)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact ⟨⟨g * b, hb⟩, Finset.mem_univ _, GS_mul_self S g b⟩
  rw [hstep1]
  calc ∑ h, α h * (if g * h ∈ LamS S then (1 : ℝ) else 0)
      = ∑ h, α h * ((Fintype.card (LamS S) : ℝ)⁻¹ * ∑ d : LamS S, (BS S d (g * h) : ℝ)) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [hchar h]
        split_ifs <;> [field_simp; simp]
    _ = _ := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun h _ => ?_
        rw [BS_mul_right' S d g h]
        push_cast; ring

end Lagrangian

end QuadFormsKB.SqDual
