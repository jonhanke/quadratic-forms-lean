/-
# Euler products over the fractional ideals

**Layer:** real series and products indexed by finitely supported exponent vectors $x : \iota \to_0 \mathbb Z$; then the
fractional ideals of a number field, $\mathfrak b \leftrightarrow (\mathrm{ord}_\mathfrak p\mathfrak b)_\mathfrak p$ (Mathlib's `FractionalIdeal.count`).

**The Euler product** (`hasSum_finsupp_finprod`): for $f_\mathfrak p : \mathbb Z \to \mathbb R_{\ge0}$ with $f_\mathfrak p(0) = 1$ outside a finite set $S_0$,
each $\sum_jf_\mathfrak p(j)$ convergent and $\prod_\mathfrak p\sum_jf_\mathfrak p(j)$ convergent (`HasProd`) to $P$,
$$\sum_{x}\prod_\mathfrak p f_\mathfrak p(x_\mathfrak p) = P.$$
*Proof:* for a finite $T \supseteq S_0$ the vectors supported in $T$ give $\prod_{\mathfrak p\in T}\sum_jf_\mathfrak p(j)$ (a finite product of
nonnegative series, `hasSum_supported`); these partial products increase with $T$ (the factors off $S_0$ are $\ge 1$) and tend
to $P$, so $P$ is the least upper bound of the partial sums (`hasSum_of_isLUB_of_nonneg`).

**For ideals** (`hasSum_fracIdeal`): the same sum over the fractional ideals $\mathfrak b$ with $x_\mathfrak p = \mathrm{ord}_\mathfrak p\mathfrak b$
(`fracIdealEquiv`, unique factorization), and $N\mathfrak b = \prod_\mathfrak pN\mathfrak p^{\mathrm{ord}_\mathfrak p\mathfrak b}$ (`idealNorm_eq_finprod`).
-/
import QuadFormsKB.Tamagawa.IdeleClass

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

/-! ### Finite products of series, indexed by finitely supported vectors -/

section Finsupp

variable {ι : Type*} [DecidableEq ι] (f : ι → ℤ → ℝ)

/-- The vectors supported in $T$. -/
abbrev SuppIn (T : Finset ι) : Type _ := {x : ι →₀ ℤ // x.support ⊆ T}

/-- $\{x : \mathrm{supp}\,x\subseteq \{a\}\cup T\} \simeq \mathbb Z\times\{x : \mathrm{supp}\,x \subseteq T\}$ for $a \notin T$. -/
def suppInsertEquiv {a : ι} {T : Finset ι} (ha : a ∉ T) : SuppIn (insert a T) ≃ ℤ × SuppIn T where
  toFun x := ((x : ι →₀ ℤ) a, ⟨(x : ι →₀ ℤ).erase a, by
    intro v hv
    rw [Finsupp.support_erase, Finset.mem_erase] at hv
    rcases Finset.mem_insert.mp (x.2 hv.2) with h | h
    · exact absurd h hv.1
    · exact h⟩)
  invFun p := ⟨(p.2 : ι →₀ ℤ) + Finsupp.single a p.1, by
    intro v hv
    have := Finsupp.support_add hv
    rcases Finset.mem_union.mp this with h | h
    · exact Finset.mem_insert_of_mem (p.2.2 h)
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; exact Finset.mem_insert_self a T⟩
  left_inv x := Subtype.ext (by
    ext v
    simp only [Finsupp.coe_add, Pi.add_apply]
    by_cases hv : v = a
    · subst hv; simp
    · rw [Finsupp.erase_ne hv, Finsupp.single_eq_of_ne hv, add_zero])
  right_inv p := by
    have hpa : (p.2 : ι →₀ ℤ) a = 0 := by
      by_contra h
      exact ha (p.2.2 (Finsupp.mem_support_iff.mpr h))
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp [hpa]
    · ext v
      by_cases hv : v = a
      · subst hv; simp [hpa]
      · simp [Finsupp.erase_ne hv]

theorem suppInsertEquiv_fst {a : ι} {T : Finset ι} (ha : a ∉ T) (x : SuppIn (insert a T)) :
    (suppInsertEquiv ha x).1 = (x : ι →₀ ℤ) a := rfl

theorem suppInsertEquiv_snd {a : ι} {T : Finset ι} (ha : a ∉ T) (x : SuppIn (insert a T)) (v : ι) (hv : v ≠ a) :
    ((suppInsertEquiv ha x).2 : ι →₀ ℤ) v = (x : ι →₀ ℤ) v := Finsupp.erase_ne hv

/-- **A finite product of nonnegative series**: $\sum_{x : \mathrm{supp}\,x\subseteq T}\prod_{\mathfrak p\in T}f_\mathfrak p(x_\mathfrak p) =
\prod_{\mathfrak p\in T}\sum_jf_\mathfrak p(j)$. -/
theorem hasSum_supported (hf0 : ∀ v j, 0 ≤ f v j) (hs : ∀ v, Summable (f v)) (T : Finset ι) :
    HasSum (fun x : SuppIn T => ∏ v ∈ T, f v ((x : ι →₀ ℤ) v)) (∏ v ∈ T, ∑' j, f v j) := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    have : Unique (SuppIn (∅ : Finset ι)) :=
      ⟨⟨⟨0, by simp⟩⟩, fun x => Subtype.ext (Finsupp.support_eq_empty.mp (Finset.subset_empty.mp x.2))⟩
    convert hasSum_fintype (fun _ : SuppIn (∅ : Finset ι) => (1 : ℝ)) using 1
    simp
  | insert a T ha ih =>
    set g : SuppIn T → ℝ := fun x => ∏ v ∈ T, f v ((x : ι →₀ ℤ) v)
    have hg0 : 0 ≤ g := fun x => Finset.prod_nonneg fun v _ => hf0 v _
    have h1 : HasSum (fun p : ℤ × SuppIn T => f a p.1 * g p.2) ((∑' j, f a j) * ∏ v ∈ T, ∑' j, f v j) :=
      HasSum.mul (hs a).hasSum ih (Summable.mul_of_nonneg (hs a) ih.summable (fun j => hf0 a j) hg0)
    have hcomp : (fun x : SuppIn (insert a T) => ∏ v ∈ insert a T, f v ((x : ι →₀ ℤ) v)) =
        (fun p : ℤ × SuppIn T => f a p.1 * g p.2) ∘ suppInsertEquiv ha := by
      funext x
      rw [Function.comp_apply, Finset.prod_insert ha, suppInsertEquiv_fst]
      congr 1
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [suppInsertEquiv_snd ha x v fun h => ha (h ▸ hv)]
    rw [Finset.prod_insert ha, hcomp, (suppInsertEquiv ha).hasSum_iff]
    exact h1

/-- **The Euler product** for finitely supported exponent vectors (see the module docstring). -/
theorem hasSum_finsupp_finprod (hf0 : ∀ v j, 0 ≤ f v j) (S₀ : Finset ι) (hf1 : ∀ v ∉ S₀, f v 0 = 1)
    (hs : ∀ v, Summable (f v)) {P : ℝ} (hP : HasProd (fun v => ∑' j, f v j) P) :
    HasSum (fun x : ι →₀ ℤ => ∏ᶠ v, f v (x v)) P := by
  classical
  set F : ι → ℝ := fun v => ∑' j, f v j
  have hF0 : ∀ v, 0 ≤ F v := fun v => tsum_nonneg (hf0 v)
  have hF1 : ∀ v ∉ S₀, 1 ≤ F v := by
    intro v hv
    have := (hs v).le_tsum 0 (fun j _ => hf0 v j)
    rw [hf1 v hv] at this
    exact this
  -- on vectors supported in `T ⊇ S₀ ∪ supp`, the finprod is the product over `T`
  have hfin : ∀ (T : Finset ι), S₀ ⊆ T → ∀ x : ι →₀ ℤ, x.support ⊆ T →
      ∏ᶠ v, f v (x v) = ∏ v ∈ T, f v (x v) := by
    intro T hT x hx
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvT
    apply hv
    have hx0 : x v = 0 := by
      by_contra h; exact hvT (hx (Finsupp.mem_support_iff.mpr h))
    show f v (x v) = 1
    rw [hx0]; exact hf1 v fun h => hvT (hT h)
  -- partial products are monotone beyond `S₀`
  have hmono : ∀ T T' : Finset ι, S₀ ⊆ T → T ⊆ T' → ∏ v ∈ T, F v ≤ ∏ v ∈ T', F v := by
    intro T T' hT hTT'
    exact Finset.prod_le_prod_of_subset_of_one_le₀ hTT' (fun v _ => hF0 v) fun v _ hvT => hF1 v fun h => hvT (hT h)
  have hle : ∀ T : Finset ι, S₀ ⊆ T → ∏ v ∈ T, F v ≤ P := by
    intro T hT
    refine ge_of_tendsto hP ?_
    filter_upwards [Filter.eventually_ge_atTop T] with T' hT'
    exact hmono T T' hT hT'
  refine hasSum_of_isLUB_of_nonneg P (fun x => finprod_nonneg fun v => hf0 v _) ⟨?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    show ∑ x ∈ s, ∏ᶠ v, f v (x v) ≤ P
    set T := S₀ ∪ s.biUnion fun x => x.support
    have hT : S₀ ⊆ T := Finset.subset_union_left
    have hsT : ∀ x ∈ s, x.support ⊆ T := fun x hx =>
      (Finset.subset_biUnion_of_mem (fun x => x.support) hx).trans Finset.subset_union_right
    have hsum := hasSum_supported f hf0 hs T
    let s' : Finset (SuppIn T) := (s.attach).map ⟨fun x => ⟨x.1, hsT x.1 x.2⟩, fun a b h => by
      apply Subtype.ext; exact congrArg (fun y : SuppIn T => (y : ι →₀ ℤ)) h⟩
    have h1 : ∑ x ∈ s, ∏ᶠ v, f v (x v) = ∑ y ∈ s', ∏ v ∈ T, f v ((y : ι →₀ ℤ) v) := by
      rw [Finset.sum_map, ← Finset.sum_attach s]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact hfin T hT x.1 (hsT x.1 x.2)
    rw [h1]
    exact (sum_le_hasSum s' (fun y _ => Finset.prod_nonneg fun v _ => hf0 v _) hsum).trans (hle T hT)
  · intro u hu
    refine le_of_tendsto hP ?_
    filter_upwards [Filter.eventually_ge_atTop S₀] with T hT
    refine hasSum_le_of_sum_le (hasSum_supported f hf0 hs T) fun s' => ?_
    have e : ∑ y ∈ s', ∏ v ∈ T, f v ((y : ι →₀ ℤ) v) =
        ∑ x ∈ s'.map ⟨Subtype.val, Subtype.val_injective⟩, ∏ᶠ v, f v (x v) := by
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun y _ => (hfin T hT y.1 y.2).symm
    rw [e]
    exact hu ⟨_, rfl⟩

end Finsupp

/-! ### Fractional ideals as exponent vectors -/

section Ideals

open IsDedekindDomain FractionalIdeal NumberField QuadFormsKB.IdeleClass
open scoped nonZeroDivisors

variable (F : Type) [Field F] [NumberField F]

/-- **The exponent vector** $(\mathrm{ord}_\mathfrak p\mathfrak b)_\mathfrak p$ of a fractional ideal (finitely supported). -/
def ordVec (𝔟 : FracIdeal F) : HeightOneSpectrum (𝓞 F) →₀ ℤ where
  support := (Filter.eventually_cofinite.mp (finite_factors (𝔟 : FractionalIdeal (𝓞 F)⁰ F))).toFinset
  toFun v := count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  mem_support_toFun v := by simp

theorem ordVec_apply (𝔟 : FracIdeal F) (v : HeightOneSpectrum (𝓞 F)) :
    ordVec F 𝔟 v = count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := rfl

theorem finprod_zpow_ne_zero (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ x v) ≠ 0 := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := x.support)]
  · exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)
  · intro v hv
    by_contra h
    apply hv
    show (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ x v = 1
    rw [Finsupp.notMem_support_iff.mp h, zpow_zero]

/-- **Unique factorization**: $\mathfrak b \mapsto (\mathrm{ord}_\mathfrak p\mathfrak b)_\mathfrak p$ is a bijection from the fractional ideals onto the
finitely supported exponent vectors, with inverse $x \mapsto \prod_\mathfrak p\mathfrak p^{x_\mathfrak p}$. -/
def fracIdealEquiv : FracIdeal F ≃ (HeightOneSpectrum (𝓞 F) →₀ ℤ) where
  toFun := ordVec F
  invFun x := Units.mk0 _ (finprod_zpow_ne_zero F x)
  left_inv 𝔟 := Units.ext (by
    rw [Units.val_mk0, ← finprod_heightOneSpectrum_factorization' F 𝔟.ne_zero]
    exact finprod_congr fun v => by rw [ordVec_apply])
  right_inv x := by
    ext v
    rw [ordVec_apply, Units.val_mk0, count_finprod F v x (Filter.eventually_cofinite.mpr
      (x.support.finite_toSet.subset fun v hv => Finsupp.mem_support_iff.mpr hv))]

theorem fracIdealEquiv_apply (𝔟 : FracIdeal F) (v : HeightOneSpectrum (𝓞 F)) :
    fracIdealEquiv F 𝔟 v = count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := ordVec_apply F 𝔟 v

/-- **The norm of a fractional ideal** $N\mathfrak b = \prod_\mathfrak pN\mathfrak p^{\mathrm{ord}_\mathfrak p\mathfrak b}$. -/
theorem idealNorm_eq_finprod (𝔟 : FracIdeal F) :
    idealNorm F 𝔟 = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      (Ideal.absNorm v.asIdeal : ℝ) ^ count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
  have hfac := finprod_heightOneSpectrum_factorization' F 𝔟.ne_zero
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).Finite := by
    refine (Filter.eventually_cofinite.mp (finite_factors (𝔟 : FractionalIdeal (𝓞 F)⁰ F))).subset fun v hv => ?_
    intro h0; apply hv; simp only [h0, zpow_zero]
  unfold idealNorm
  conv_lhs => rw [← hfac]
  have hmap : absNorm (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        absNorm ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :=
    (absNorm (R := 𝓞 F) (K := F)).toMonoidHom.map_finprod hfin
  have hfin' : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      absNorm ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F))).Finite :=
    hfin.subset fun v hv h => hv (by simp only at h ⊢; rw [h, map_one])
  rw [hmap, show ((∏ᶠ v : HeightOneSpectrum (𝓞 F),
      absNorm ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : ℚ) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        ((absNorm ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : ℚ) : ℝ) from
    (Rat.castHom ℝ).toMonoidHom.map_finprod hfin']
  refine finprod_congr fun v => ?_
  rw [map_zpow₀, coeIdeal_absNorm]
  push_cast
  rfl

end Ideals

end QuadFormsKB.Tamagawa
