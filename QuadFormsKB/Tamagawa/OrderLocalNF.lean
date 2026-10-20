/-
# Local orders without bases

**Layer:** $F$ a number field (class number arbitrary), $D=(a,b)_F$ with $a,b \in \mathcal O_F$, $\mathcal O \subset D$ an $\mathcal O_F$-order, $v$ a finite
place. The PID file `QuatOrderGlobal` uses an $\mathcal O_F$-basis of $\mathcal O$ to see that the completion $\mathcal O_v$ is an order and is maximal.
Here we replace the global basis by a **local frame** (`LocFrame`): an $F$-basis $f$ of $D$ inside $\mathcal O$ such that the
$R_v$-span of $\mathcal O$ ($R_v=(\mathcal O_F)_{\mathfrak p_v}$, Mathlib's `valuationSubringAtPrime`, a PID) is $\oplus R_v f_i$; it exists by
local freeness (`LocFrame.exists`: fg torsion-free over the PID $R_v$). No basis or generator of any ideal of $\mathcal O_F$ is chosen.

Sources: Voight, *Quaternion Algebras* (2021), Lemma 9.5.3, Lemma 10.4.3.
-/
import QuadFormsKB.Tamagawa.QuatOrderGlobal

open NumberField IsDedekindDomain Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF IsLocalization IsLocalRing WithZero

section LocFrame

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a b : 𝓞 F}

/-- The localization $R_v = (\mathcal O_F)_{\mathfrak p_v} \subset F$ (Mathlib's `valuationSubringAtPrime`), a DVR. -/
abbrev LocR := HeightOneSpectrum.valuationSubringAtPrime F v

theorem mem_locR_iff {c : F} : c ∈ LocR v ↔ v.valuation F c ≤ 1 := by
  change c ∈ HeightOneSpectrum.valuationSubringAtPrime F v ↔ _
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact Valuation.mem_valuationSubring_iff _ _

variable {v}

/-- Denominators prime to $v$ clear the $R_v$-span of $\mathcal O$. -/
theorem exists_notMem_smul_mem {O : Subalgebra (𝓞 F) (QuatF F a b)} {z : QuatF F a b}
    (hz : z ∈ Submodule.span (LocR v) (O : Set (QuatF F a b))) :
    ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ s • z ∈ O := by
  induction hz using Submodule.span_induction with
  | mem y hy => exact ⟨1, fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rw [smul_zero]; exact O.zero_mem⟩
  | add y w _ _ hy hw =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htw⟩ := hw
    refine ⟨s * t, v.isPrime.mul_notMem hs ht, ?_⟩
    have h1 : (s * t) • y = t • (s • y) := by rw [mul_comm, mul_smul]
    have h2 : (s * t) • w = s • (t • w) := mul_smul _ _ _
    rw [smul_add, h1, h2]
    exact O.add_mem (O.smul_mem hsy _) (O.smul_mem htw _)
  | smul r y _ hy =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (r : F) ((mem_locR_iff v).1 r.2)
    refine ⟨s * d, v.isPrime.mul_notMem hs d.2, ?_⟩
    have : (s * d) • (r • y) = n • (s • y) := by
      rw [← algebraMap_smul F (s * d), ← algebraMap_smul F n, ← algebraMap_smul F s,
        ← algebraMap_smul F (r : LocR v) y]
      rw [smul_smul, smul_smul, map_mul]
      congr 1
      have hr : (algebraMap (LocR v) F) r = (r : F) := rfl
      rw [hr, ← hnd]; ring
    rw [this]; exact O.smul_mem hsy _

variable (v) in
/-- **A local frame of an order at $v$:** an $F$-basis $f$ of $D$ inside $\mathcal O$ whose $R_v$-span is the
$R_v$-span of $\mathcal O$ (every element of $\mathcal O$ has $v$-integral coordinates). It replaces an
$\mathcal O_F$-basis of $\mathcal O$ when $\mathcal O_F$ is not a PID (only the local freeness of $\mathcal O$ is used). -/
structure LocFrame (O : Subalgebra (𝓞 F) (QuatF F a b)) where
  fb : Module.Basis (Fin 4) F (QuatF F a b)
  mem : ∀ i, fb i ∈ O
  integral : ∀ x ∈ O, ∀ i, v.valuation F (fb.repr x i) ≤ 1

theorem LocFrame.exists {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    Nonempty (LocFrame v O) := by
  classical
  have : Module.IsTorsionFree (LocR v) (QuatF F a b) :=
    Module.IsTorsionFree.comap (S := F) (fun r : LocR v => (r : F))
      (fun r hr => IsRegular.of_ne_zero (fun h0 => hr.ne_zero (Subtype.ext h0))) (fun r m => rfl)
  set OR : Submodule (LocR v) (QuatF F a b) := Submodule.span (LocR v) (O : Set (QuatF F a b)) with hOR
  have hfg : Module.Finite (LocR v) OR := by
    obtain ⟨S, hS⟩ := hO.fg
    refine Module.Finite.iff_fg.2 ⟨S, ?_⟩
    apply le_antisymm
    · rw [Submodule.span_le]
      intro s hs
      exact Submodule.subset_span (show s ∈ (Subalgebra.toSubmodule O : Set _) from hS ▸ Submodule.subset_span hs)
    · rw [hOR, Submodule.span_le]
      intro o ho
      have ho' : o ∈ Submodule.span (𝓞 F) (S : Set (QuatF F a b)) := by
        have h : o ∈ Subalgebra.toSubmodule O := ho
        rwa [← hS] at h
      exact Submodule.span_le_restrictScalars (𝓞 F) (LocR v) _ ho'
  have hfree : Module.Free (LocR v) OR := Module.free_of_finite_type_torsion_free'
  let b' : Module.Basis (Module.Free.ChooseBasisIndex (LocR v) OR) (LocR v) OR := Module.Free.chooseBasis _ _
  let g : Module.Free.ChooseBasisIndex (LocR v) OR → QuatF F a b := fun i => (b' i : QuatF F a b)
  have hgR : LinearIndependent (LocR v) g := b'.linearIndependent.map' OR.subtype (Submodule.ker_subtype _)
  have hgF : LinearIndependent F g := hgR.localization F (nonZeroDivisors (LocR v))
  have hrepr : ∀ x ∈ O, ∃ r : Module.Free.ChooseBasisIndex (LocR v) OR → LocR v, x = ∑ i, (r i : F) • g i := by
    intro x hx
    have hx' : x ∈ OR := Submodule.subset_span hx
    refine ⟨fun i => b'.repr ⟨x, hx'⟩ i, ?_⟩
    have h := congrArg Subtype.val (b'.sum_repr (⟨x, hx'⟩ : OR))
    rw [Submodule.coe_sum] at h
    refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rfl
  have hspan : ⊤ ≤ Submodule.span F (Set.range g) := by
    rw [← hO.span, Submodule.span_le]
    intro x hx
    obtain ⟨r, rfl⟩ := hrepr x hx
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let fb' := Module.Basis.mk hgF hspan
  choose s hs hsg using fun i => exists_notMem_smul_mem (v := v) (O := O) (b' i).2
  have hsF : ∀ i, algebraMap (𝓞 F) F (s i) ≠ 0 := fun i h0 =>
    hs i (by
      have : s i = 0 := (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1 h0
      rw [this]; exact v.asIdeal.zero_mem)
  have hvs : ∀ i, v.valuation F (algebraMap (𝓞 F) F (s i)) = 1 := fun i => by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_eq_one_iff_mem_primeCompl (s i)).2 (hs i)
  let w : Module.Free.ChooseBasisIndex (LocR v) OR → Fˣ := fun i => Units.mk0 _ (hsF i)
  let fb1 := fb'.unitsSMul w
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (LocR v) OR) = 4 := by
    rw [← Module.finrank_eq_card_basis fb', QuaternionAlgebra.finrank_eq_four]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨fb1.reindex e, fun i => ?_, fun x hx j => ?_⟩⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.unitsSMul_apply, Module.Basis.mk_apply]
    have := hsg (e.symm i)
    rw [← algebraMap_smul F] at this
    exact this
  · obtain ⟨r, rfl⟩ := hrepr x hx
    rw [Module.Basis.repr_reindex_apply, Module.Basis.repr_unitsSMul]
    have : fb'.repr (∑ i, (r i : F) • g i) (e.symm j) = (r (e.symm j) : F) := by
      have h2 : (∑ i, (r i : F) • g i) = ∑ i, (r i : F) • fb' i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Module.Basis.mk_apply]
      rw [h2, Module.Basis.repr_sum_self]
    rw [this]
    change v.valuation F (((w (e.symm j))⁻¹ : Fˣ) * (r (e.symm j) : F)) ≤ 1
    rw [map_mul, Units.val_inv_eq_inv_val]
    simp only [w, Units.val_mk0, map_inv₀, hvs, inv_one, one_mul]
    exact (mem_locR_iff v).1 (r _).2

namespace LocFrame

variable {O : Subalgebra (𝓞 F) (QuatF F a b)} (L : LocFrame v O)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $c \in F$ is $v$-integral iff its image in $F_v$ lies in $\mathfrak o_v$. -/
theorem isInteger_algebraMap_iff (c : F) :
    IsInteger 𝔬 (algebraMap F Fv c) ↔ v.valuation F c ≤ 1 := by
  constructor
  · rintro ⟨d, hd⟩
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have : (algebraMap F Fv c) = (d : Fv) := hd.symm
    change Valued.v (algebraMap F Fv c) ≤ 1
    rw [this]; exact d.2
  · intro h
    refine ⟨⟨algebraMap F Fv c, ?_⟩, rfl⟩
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h

/-- The images $E_i = \iota(f_i) \in D_v$ of the frame. -/
def cvec (i : Fin 4) : QuatV v a b := complHom v a b (L.fb i)

theorem complHom_eq_sum (x : QuatF F a b) :
    complHom v a b x = ∑ i, algebraMap F Fv (L.fb.repr x i) • L.cvec i := by
  conv_lhs => rw [← L.fb.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, algebraMap_smul]; rfl

theorem top_le_span_cvec : ⊤ ≤ Submodule.span Fv (Set.range L.cvec) := by
  set S := Submodule.span Fv (Set.range L.cvec)
  have hall : ∀ x : QuatF F a b, complHom v a b x ∈ S := by
    intro x
    rw [L.complHom_eq_sum x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro y _
  rw [eq_sum_basis y]
  have h1 : (1 : QuatV v a b) ∈ S := by rw [← map_one (complHom v a b)]; exact hall 1
  have hi : (qi : QuatV v a b) ∈ S := by rw [← complHom_qi (v := v) a b]; exact hall _
  have hj : (qj : QuatV v a b) ∈ S := by rw [← complHom_qj (v := v) a b]; exact hall _
  have hk : (qk : QuatV v a b) ∈ S := by rw [← complHom_qk (v := v) a b]; exact hall _
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ h1) (S.smul_mem _ hi)) (S.smul_mem _ hj)) (S.smul_mem _ hk)

/-- The frame is an $F_v$-basis of $D_v$. -/
def cb : Module.Basis (Fin 4) Fv (QuatV v a b) :=
  basisOfTopLeSpanOfCardEqFinrank L.cvec L.top_le_span_cvec
    (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])

@[simp] theorem cb_apply (i : Fin 4) : L.cb i = L.cvec i := by
  rw [cb, coe_basisOfTopLeSpanOfCardEqFinrank]

theorem cb_repr_complHom (x : QuatF F a b) (i : Fin 4) :
    L.cb.repr (complHom v a b x) i = algebraMap F Fv (L.fb.repr x i) := by
  rw [L.complHom_eq_sum x]
  have : (∑ i, algebraMap F Fv (L.fb.repr x i) • L.cvec i) = ∑ i, algebraMap F Fv (L.fb.repr x i) • L.cb i := by
    simp only [cb_apply]
  rw [this, Module.Basis.repr_sum_self]

theorem localOrder_eq_span :
    Subalgebra.toSubmodule (localOrder (v := v) a b O) = Submodule.span 𝔬 (Set.range L.cvec) := by
  apply le_antisymm
  · change Submodule.span 𝔬 _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [L.complHom_eq_sum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨d, hd⟩ := (isInteger_algebraMap_iff _).2 (L.integral x hx i)
    rw [← hd, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_localOrder_of_mem a b (L.mem i)

/-- **Membership in $\mathcal O_v$ by coordinates** in the frame. -/
theorem mem_localOrder_iff (y : QuatV v a b) :
    y ∈ localOrder (v := v) a b O ↔ ∀ i, IsInteger 𝔬 (L.cb.repr y i) := by
  constructor
  · intro hy
    have hy' : y ∈ Submodule.span 𝔬 (Set.range L.cvec) := by
      rw [← L.localOrder_eq_span]; exact hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro i
      rw [← L.cb_apply, Module.Basis.repr_self]
      by_cases h : j = i
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro i
      obtain ⟨p, hp⟩ := hy i; obtain ⟨q, hq⟩ := hz i
      exact ⟨p + q, by rw [map_add, hp, hq, map_add, Finsupp.add_apply]⟩
    | smul c y _ hy =>
      intro i
      obtain ⟨p, hp⟩ := hy i
      refine ⟨c * p, ?_⟩
      rw [← algebraMap_smul Fv c y, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hp]
  · intro h
    choose c hc using h
    rw [← L.cb.sum_repr y]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [← hc i, algebraMap_smul, cb_apply]
    exact Subalgebra.smul_mem _ (mem_localOrder_of_mem a b (L.mem i)) _

include L in
/-- **The completion of an order is an order** (no PID hypothesis). -/
theorem isOrder_localOrder : IsOrder 𝔬 Fv (localOrder (v := v) a b O) := by
  refine ⟨?_, ?_⟩
  · rw [L.localOrder_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  · refine eq_top_iff.2 (L.top_le_span_cvec.trans (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact mem_localOrder_of_mem a b (L.mem i)

end LocFrame
end LocFrame
section Unif

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- **A fractional uniformizing power** (no generator of $\mathfrak p_v^N$ is used): there is $u\in F$ with $v(u)=e^{N}$ and
$u\,\mathfrak p_v^N\subseteq\mathcal O_F$. -/
theorem exists_unif_inv (N : ℕ) : ∃ u : F, v.valuation F u = exp (N : ℤ) ∧
    ∀ y ∈ v.asIdeal ^ N, ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = u * algebraMap (𝓞 F) F y := by
  obtain ⟨a, haN, haN1⟩ := IsConcreteLE.exists_of_lt (Ideal.pow_succ_lt_pow v.ne_bot N)
  have ha0 : a ≠ 0 := fun h => haN1 (h ▸ Ideal.zero_mem _)
  have hle : Ideal.span {a} ≤ v.asIdeal ^ N := (Ideal.span_singleton_le_iff_mem _).2 haN
  obtain ⟨𝔟, h𝔟⟩ := (Ideal.dvd_iff_le).2 hle
  have hb : ¬ 𝔟 ≤ v.asIdeal := fun h => by
    apply haN1
    have : Ideal.span {a} ≤ v.asIdeal ^ N * v.asIdeal := by rw [h𝔟]; exact Ideal.mul_mono_right h
    rw [← pow_succ] at this
    exact this (Ideal.mem_span_singleton_self a)
  obtain ⟨b, hb𝔟, hbp⟩ := IsConcreteLE.not_le_iff_exists.1 hb
  have hva : v.intValuation a = exp (-(N : ℤ)) := by
    have h1 : v.intValuation a ≤ exp (-(N : ℤ)) := (v.intValuation_le_pow_iff_mem a N).2 haN
    have h2 : ¬ v.intValuation a ≤ exp (-((N + 1 : ℕ) : ℤ)) := fun h => haN1 ((v.intValuation_le_pow_iff_mem a (N+1)).1 h)
    have hne : v.intValuation a ≠ 0 := (v.intValuation_ne_zero a ha0)
    obtain ⟨z, hz⟩ : ∃ z : ℤ, v.intValuation a = exp z := ⟨log (v.intValuation a), (exp_log hne).symm⟩
    rw [hz, exp_le_exp] at h1 h2
    rw [hz]; congr 1; push_cast at h2; omega
  have hvb : v.intValuation b = 1 := (v.intValuation_eq_one_iff_mem_primeCompl b).2 hbp
  have haF : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha0
  refine ⟨algebraMap (𝓞 F) F b / algebraMap (𝓞 F) F a, ?_, fun y hy => ?_⟩
  · rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hva, hvb]
    rw [← exp_zero, ← exp_sub]; congr 1; ring
  · have hyb : y * b ∈ Ideal.span {a} := by
      rw [h𝔟]; exact Ideal.mul_mem_mul hy hb𝔟
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyb
    refine ⟨c, ?_⟩
    field_simp
    rw [← map_mul, ← map_mul, hc]; ring_nf
end Unif

section Maximal

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Every $c \in F_v$ becomes integral after multiplying by a power of the uniformizer $\pi_v$. -/
theorem exists_pow_mul_isInteger_π (c : Fv) :
    ∃ N : ℕ, IsInteger 𝔬 (algebraMap 𝔬 Fv (π v) ^ N * c) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝔬) c
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 (irreducible_π v)
  refine ⟨n, x * ↑u⁻¹, ?_⟩
  have hu0 : algebraMap 𝔬 Fv (u : 𝔬) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 u.ne_zero
  have hp0 : algebraMap 𝔬 Fv (π v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (irreducible_π v).ne_zero
  have huinv : algebraMap 𝔬 Fv (↑u⁻¹ : 𝔬) = (algebraMap 𝔬 Fv (u : 𝔬))⁻¹ := by
    have h1 := congrArg (algebraMap 𝔬 Fv) u.inv_mul
    rw [map_mul, map_one] at h1
    exact (inv_eq_of_mul_eq_one_left h1).symm
  rw [hu, map_mul, map_mul, map_pow, huinv]
  field_simp

/-- The global ring $\{x\in D:\ \iota(x)\in\mathcal O'_v,\ \mathfrak p_v^m x\subseteq\mathcal O \text{ for some } m\}$ attached to an order
$\mathcal O$ and an $\mathfrak o_v$-subalgebra $\mathcal O'_v\subseteq D_v$ (basis- and generator-free version of `liftOrder`). -/
def liftOrderNF (O : Subalgebra (𝓞 F) (QuatF F a b)) (O' : Subalgebra 𝔬 (QuatV v a b)) :
    Subalgebra (𝓞 F) (QuatF F a b) where
  carrier := {x | complHom v a b x ∈ O' ∧ ∃ m : ℕ, ∀ y ∈ v.asIdeal ^ m, y • x ∈ O}
  mul_mem' := by
    rintro x x' ⟨hx, m, hm⟩ ⟨hx', n, hn⟩
    refine ⟨by rw [map_mul]; exact O'.mul_mem hx hx', m + n, fun y hy => ?_⟩
    rw [pow_add] at hy
    refine Submodule.mul_induction_on (C := fun y => y • (x * x') ∈ O) hy (fun y1 h1 y2 h2 => ?_)
      (fun y y' h h' => ?_)
    · have : (y1 * y2) • (x * x') = (y1 • x) * (y2 • x') := by
        rw [← algebraMap_smul F (y1 * y2), ← algebraMap_smul F y1, ← algebraMap_smul F y2, smul_mul_smul_comm, map_mul]
      rw [this]; exact O.mul_mem (hm _ h1) (hn _ h2)
    · rw [add_smul]; exact O.add_mem h h'
  one_mem' := ⟨by rw [map_one]; exact O'.one_mem, 0, fun y _ => by
    convert O.algebraMap_mem y using 1
    exact (Algebra.algebraMap_eq_smul_one y).symm⟩
  add_mem' := by
    rintro x x' ⟨hx, m, hm⟩ ⟨hx', n, hn⟩
    refine ⟨by rw [map_add]; exact O'.add_mem hx hx', m + n, fun y hy => ?_⟩
    rw [smul_add]
    exact O.add_mem (hm y (Ideal.pow_le_pow_right (Nat.le_add_right m n) hy))
      (hn y (Ideal.pow_le_pow_right (Nat.le_add_left n m) hy))
  zero_mem' := ⟨by rw [map_zero]; exact O'.zero_mem, 0, fun y _ => by rw [smul_zero]; exact O.zero_mem⟩
  algebraMap_mem' := fun r => by
    refine ⟨?_, 0, fun y _ => ?_⟩
    · have h1 : complHom v a b (algebraMap (𝓞 F) (QuatF F a b) r) = algebraMap 𝔬 (QuatV v a b) (ι v r) := by
        rw [IsScalarTower.algebraMap_apply (𝓞 F) F (QuatF F a b), AlgHom.commutes,
          IsScalarTower.algebraMap_apply 𝔬 Fv (QuatV v a b), IsScalarTower.algebraMap_apply F Fv (QuatV v a b)]
        rfl
      change complHom v a b (algebraMap (𝓞 F) (QuatF F a b) r) ∈ O'
      rw [h1]
      exact O'.algebraMap_mem _
    · convert O.algebraMap_mem (y * r) using 1
      rw [map_mul]; exact Algebra.smul_def (A := QuatF F a b) y _


set_option maxHeartbeats 800000 in
/-- **Maximality is local, no PID (one direction): the completion of a maximal order is maximal.** For $\mathcal O$ a maximal
$\mathcal O_F$-order of $D=(a,b)_F$ ($\mathcal O_F$ of any class number) and $v$ a finite place, $\mathcal O_v$ is a maximal
$\mathfrak o_v$-order of $D_v$. The proof of `isMaximalOrder_localOrder` with the global $\mathcal O_F$-basis replaced by a local frame
and the powers of a generator $\varpi$ of $\mathfrak p_v$ replaced by the ideal powers $\mathfrak p_v^m$ (colon lattices).

Source: Voight 2021, Lemma 10.4.3 and Lemma 9.5.3. -/
theorem isMaximalOrder_localOrder_nf {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O) :
    IsMaximalOrder 𝔬 Fv (localOrder (v := v) a b O) := by
  classical
  obtain ⟨L⟩ := LocFrame.exists (v := v) hO.1
  refine ⟨L.isOrder_localOrder, fun O' hO' hle => ?_⟩
  set π' : 𝔬 := π v with hπ'
  have hπ0 : algebraMap 𝔬 Fv π' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (irreducible_π v).ne_zero
  have hvπ : Valued.v (algebraMap 𝔬 Fv π') = exp (-1 : ℤ) := valued_π v
  -- Step A: a power of π' moves O' into O_v
  have hA1 : ∀ z : QuatV v a b, ∃ N : ℕ, ∀ M, N ≤ M → π' ^ M • z ∈ localOrder (v := v) a b O := by
    intro z
    have : ∀ i, ∃ N : ℕ, IsInteger 𝔬 (algebraMap 𝔬 Fv π' ^ N * L.cb.repr z i) := fun i =>
      exists_pow_mul_isInteger_π _
    choose Ni hNi using this
    refine ⟨Finset.univ.sup Ni, fun M hM => ?_⟩
    rw [L.mem_localOrder_iff]
    intro i
    have hle' : Ni i ≤ M := (Finset.le_sup (Finset.mem_univ i)).trans hM
    obtain ⟨t, ht⟩ := hNi i
    refine ⟨π' ^ (M - Ni i) * t, ?_⟩
    rw [← algebraMap_smul Fv (π' ^ M) z, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ht, map_pow,
      map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle']
  choose Nz hNz using hA1
  obtain ⟨S, hS⟩ := hO'.fg
  set N := S.sup Nz with hNdef
  have hN : ∀ z ∈ O', π' ^ N • z ∈ localOrder (v := v) a b O := by
    intro z hz
    have hz' : z ∈ Submodule.span 𝔬 (S : Set (QuatV v a b)) := by rw [hS]; exact hz
    clear hz
    induction hz' using Submodule.span_induction with
    | mem y hy => exact hNz y N (Finset.le_sup hy)
    | zero => rw [smul_zero]; exact Subalgebra.zero_mem _
    | add y w _ _ hy hw => rw [smul_add]; exact Subalgebra.add_mem _ hy hw
    | smul c y _ hy => rw [smul_comm]; exact Subalgebra.smul_mem _ hy _
  -- Step C: p^N O'' ⊆ O
  have hK : ∀ x : QuatF F a b, complHom v a b x ∈ O' → ∀ m : ℕ, (∀ y ∈ v.asIdeal ^ m, y • x ∈ O) →
      ∀ y ∈ v.asIdeal ^ N, y • x ∈ O := by
    intro x hx m hm y hy
    rcases le_or_gt m N with hmN | hmN
    · exact hm y (Ideal.pow_le_pow_right hmN hy)
    · have hcoord : ∀ i, v.valuation F (L.fb.repr x i) ≤ exp (N : ℤ) := by
        intro i
        have h1 := (L.mem_localOrder_iff _).1 (hN _ hx) i
        rw [← algebraMap_smul Fv (π' ^ N) (complHom v a b x), map_smul, Finsupp.smul_apply, smul_eq_mul,
          LocFrame.cb_repr_complHom] at h1
        obtain ⟨d, hd⟩ := h1
        have hdv : Valued.v (d : Fv) ≤ 1 := d.2
        have hvc : Valued.v (algebraMap F Fv (L.fb.repr x i)) = v.valuation F (L.fb.repr x i) :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
        have hprod : exp (-(N : ℤ)) * v.valuation F (L.fb.repr x i) ≤ 1 := by
          have : Valued.v (algebraMap 𝔬 Fv (π' ^ N) * algebraMap F Fv (L.fb.repr x i)) =
              exp (-(N : ℤ)) * v.valuation F (L.fb.repr x i) := by
            rw [map_mul, hvc, map_pow, map_pow, hvπ, ← exp_nsmul]; simp
          rw [← this, ← hd]; exact hdv
        calc v.valuation F (L.fb.repr x i) = exp (N : ℤ) * (exp (-(N : ℤ)) * v.valuation F (L.fb.repr x i)) := by
              rw [← mul_assoc, ← exp_add]; simp
          _ ≤ exp (N : ℤ) * 1 := mul_le_mul' le_rfl hprod
          _ = exp (N : ℤ) := mul_one _
      have hyv : v.valuation F (algebraMap (𝓞 F) F y) ≤ exp (-(N : ℤ)) := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]; exact (v.intValuation_le_pow_iff_mem y N).2 hy
      have hmemR : ∀ i, algebraMap (𝓞 F) F y * L.fb.repr x i ∈ LocR v := fun i => by
        rw [mem_locR_iff, map_mul]
        calc _ ≤ exp (-(N : ℤ)) * exp (N : ℤ) := mul_le_mul' hyv (hcoord i)
          _ = 1 := by rw [← exp_add]; simp
      have hz : y • x ∈ Submodule.span (LocR v) (O : Set (QuatF F a b)) := by
        rw [show y • x = ∑ i, y • (L.fb.repr x i • L.fb i) from by
          conv_lhs => rw [← L.fb.sum_repr x]
          rw [Finset.smul_sum]]
        refine Submodule.sum_mem _ fun i _ => ?_
        have : y • (L.fb.repr x i • L.fb i) = (⟨_, hmemR i⟩ : LocR v) • L.fb i := by
          rw [← algebraMap_smul F y, smul_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (L.mem i))
      obtain ⟨s, hs, hsz⟩ := exists_notMem_smul_mem hz
      obtain ⟨k, hmk⟩ : ∃ k, m = k + N := ⟨m - N, by omega⟩
      have hsup1 : v.asIdeal ⊔ Ideal.span {s} = ⊤ := by
        by_contra hne
        have := v.isMaximal.eq_of_le hne le_sup_left
        exact hs (this ▸ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s)))
      have hcop : IsCoprime (v.asIdeal ^ k) (Ideal.span {s}) :=
        ((Ideal.isCoprime_iff_sup_eq).2 hsup1).pow_left
      have hsup : v.asIdeal ^ k ⊔ Ideal.span {s} = ⊤ := (Ideal.isCoprime_iff_sup_eq).1 hcop
      obtain ⟨t, ht, r, hr, htr⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 F) ∈ v.asIdeal ^ k ⊔ Ideal.span {s})
      have e : y • x = t • (y • x) + r • (y • x) := by rw [← add_smul, htr, one_smul]
      rw [e]
      refine O.add_mem ?_ ?_
      · rw [smul_smul]
        exact hm _ (by rw [hmk, pow_add]; exact Ideal.mul_mem_mul ht hy)
      · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hr
        rw [← hc, mul_smul]
        exact O.smul_mem hsz c
  set O'' := liftOrderNF (v := v) O O' with hO''def
  have hOO'' : O ≤ O'' := fun x hx => ⟨hle (mem_localOrder_of_mem a b hx), 0, fun y _ => O.smul_mem hx y⟩
  have hO''ord : IsOrder (𝓞 F) F O'' := by
    refine ⟨?_, eq_top_iff.2 (hO.1.span.symm.le.trans (Submodule.span_mono fun x hx => hOO'' hx))⟩
    obtain ⟨y0, hy0N, hy00⟩ : ∃ y0 ∈ v.asIdeal ^ N, y0 ≠ 0 := by
      have : v.asIdeal ^ N ≠ ⊥ := pow_ne_zero N v.ne_bot
      exact Submodule.exists_mem_ne_zero_of_ne_bot this
    have hy0F : algebraMap (𝓞 F) F y0 ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hy00
    set Lm : QuatF F a b →ₗ[𝓞 F] QuatF F a b := ((((algebraMap (𝓞 F) F y0)⁻¹ : F) • LinearMap.id :
          QuatF F a b →ₗ[F] QuatF F a b).restrictScalars (𝓞 F)) with hLm
    have hsub : Subalgebra.toSubmodule O'' ≤ (Subalgebra.toSubmodule O).map Lm := by
      rintro x ⟨hx, m, hm⟩
      refine ⟨y0 • x, hK x hx m hm y0 hy0N, ?_⟩
      change ((algebraMap (𝓞 F) F y0)⁻¹ : F) • (y0 • x) = x
      rw [← algebraMap_smul F y0 x, smul_smul, inv_mul_cancel₀ hy0F, one_smul]
    have hN' : IsNoetherian (𝓞 F) ((Subalgebra.toSubmodule O).map Lm) :=
      isNoetherian_of_fg_of_noetherian _ (hO.1.fg.map Lm)
    exact @Submodule.FG.of_le_of_isNoetherian _ _ _ _ _ _ _ hN' hsub
  have heq : O'' = O := hO.2 O'' hO''ord hOO''
  -- Step B
  refine le_antisymm (fun y hy => ?_) hle
  obtain ⟨u, huv, hu⟩ := exists_unif_inv v N
  have hy1 := (L.mem_localOrder_iff _).1 (hN y hy)
  choose d hd using hy1
  set ε : Fv := algebraMap F Fv u * algebraMap 𝔬 Fv π' ^ N with hε
  have hεv : Valued.v ε = 1 := by
    have hvu : Valued.v (algebraMap F Fv u) = exp (N : ℤ) := by
      rw [← huv]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v u
    rw [hε, map_mul, hvu, map_pow, hvπ, ← exp_nsmul, ← exp_add]; simp
  have hε0 : ε ≠ 0 := fun h => by rw [h, map_zero] at hεv; exact zero_ne_one hεv
  let e0 : 𝔬 := ⟨ε, hεv.le⟩
  let e1 : 𝔬 := ⟨ε⁻¹, show Valued.v ε⁻¹ ≤ 1 by rw [map_inv₀, hεv, inv_one]⟩
  have he10 : e1 * e0 = 1 := Subtype.ext (inv_mul_cancel₀ hε0)
  have hr := fun i => redHom_surjective v N (Ideal.Quotient.mk _ (e1 * d i))
  choose r hr using hr
  have hg : ∀ i, ∃ g : 𝔬, g * π' ^ N = e1 * d i - ι v (r i) := by
    intro i
    have : e1 * d i - ι v (r i) ∈ Ideal.span {π' ^ N} := by
      rw [← Ideal.Quotient.eq]; exact (hr i).symm
    exact Ideal.mem_span_singleton'.1 this
  choose g hg using hg
  set x : QuatF F a b := u • ∑ i, r i • L.fb i with hx
  have hxsum : ∑ i, r i • L.fb i ∈ O := Subalgebra.sum_mem _ fun i _ => O.smul_mem (L.mem i) _
  have hcx : ∀ i, L.cb.repr (complHom v a b x) i = algebraMap F Fv u * algebraMap 𝔬 Fv (ι v (r i)) := by
    intro i
    have h1 : L.fb.repr x i = u * algebraMap (𝓞 F) F (r i) := by
      rw [hx, map_smul, Finsupp.smul_apply, smul_eq_mul]
      congr 1
      have : ∑ j, r j • L.fb j = ∑ j, algebraMap (𝓞 F) F (r j) • L.fb j := by simp only [algebraMap_smul]
      rw [this, Module.Basis.repr_sum_self]
    rw [LocFrame.cb_repr_complHom, h1, map_mul]; rfl
  have hdiff : ∀ i, L.cb.repr (y - complHom v a b x) i = algebraMap 𝔬 Fv (e0 * g i) := by
    intro i
    have hE1 : algebraMap 𝔬 Fv e1 = ε⁻¹ := rfl
    have hE0 : algebraMap 𝔬 Fv e0 = ε := rfl
    have hD : algebraMap 𝔬 Fv (d i) = algebraMap 𝔬 Fv π' ^ N * L.cb.repr y i := by
      rw [hd i, ← algebraMap_smul Fv (π' ^ N) y, map_smul, Finsupp.smul_apply, smul_eq_mul, map_pow]
    have hG := congrArg (algebraMap 𝔬 Fv) (hg i)
    rw [map_mul, map_sub, map_mul, map_pow, hE1, hD] at hG
    have hū : algebraMap F Fv u ≠ 0 := left_ne_zero_of_mul hε0
    have hPN : algebraMap 𝔬 Fv π' ^ N ≠ 0 := pow_ne_zero _ hπ0
    rw [map_sub, Finsupp.sub_apply, hcx i, map_mul, hE0]
    have hεdef : ε = algebraMap F Fv u * algebraMap 𝔬 Fv π' ^ N := rfl
    have hR : algebraMap 𝔬 Fv (ι v (r i)) = ε⁻¹ * (algebraMap 𝔬 Fv π' ^ N * L.cb.repr y i) -
        algebraMap 𝔬 Fv (g i) * algebraMap 𝔬 Fv π' ^ N := by rw [hG]; ring
    rw [hR, hεdef]
    field_simp
    ring
  have hdiffO : y - complHom v a b x ∈ localOrder (v := v) a b O :=
    (L.mem_localOrder_iff _).2 fun i => ⟨_, (hdiff i).symm⟩
  have hxO' : complHom v a b x ∈ O' := by
    have : complHom v a b x = y - (y - complHom v a b x) := by abel
    rw [this]; exact O'.sub_mem hy (hle hdiffO)
  have hxO'' : x ∈ O'' := by
    refine ⟨hxO', N, fun y' hy' => ?_⟩
    obtain ⟨c, hc⟩ := hu y' hy'
    have : y' • x = c • ∑ i, r i • L.fb i := by
      rw [hx, ← algebraMap_smul F y', ← algebraMap_smul F c, hc, smul_smul, mul_comm]
    rw [this]; exact O.smul_mem hxsum c
  have hxO : x ∈ O := heq ▸ hxO''
  have : y = complHom v a b x + (y - complHom v a b x) := by abel
  rw [this]
  exact (localOrder (v := v) a b O).add_mem (mem_localOrder_of_mem a b hxO) hdiffO
end Maximal

section LocalStructure

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem algebraMap_two_mul_ne_zero_nf (ha : a ≠ 0) (hb : b ≠ 0) :
    algebraMap 𝔬 Fv (2 * ι v a * ι v b) ≠ 0 := by
  rw [map_mul, map_mul]
  refine mul_ne_zero (mul_ne_zero (by simp) ?_) ?_
  · exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha)
  · exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v hb)

/-- **At a ramified place the completion of a maximal order is the valuation ring:** if $D_v$ is a division algebra
($\operatorname{nrd}x = 0 \Rightarrow x = 0$) and $\mathcal O$ is a maximal order of $D$ ($ab \ne 0$), then
$\mathcal O_v = \{x \in D_v : \operatorname{nrd}x \in \mathfrak o_v\}$ (`valOrder`).

Source: Voight 2021, Lemma 10.4.3 and Prop. 13.3.4. -/
@[kb "voight2021" "Prop. 13.3.4; Lemma 10.4.3"]
theorem localOrder_eq_valOrder_nf (ha : a ≠ 0) (hb : b ≠ 0) {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsMaximalOrder (𝓞 F) F O) (hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0) :
    localOrder (v := v) a b O = valOrder (R := 𝔬) hdiv :=
  eq_valOrder_of_isMaximalOrder (R := 𝔬) (a := ι v a) (b := ι v b) hdiv (algebraMap_two_mul_ne_zero_nf ha hb)
    (isMaximalOrder_localOrder_nf hO)

/-- **At a split place the completion of a maximal order is $M_2(\mathfrak o_v)$:** if $D_v \cong M_2(F_v)$ and $\mathcal O$ is a
maximal order of $D$, there is an $F_v$-algebra isomorphism $\varphi : D_v \cong M_2(F_v)$ with $\varphi(\mathcal O_v) = M_2(\mathfrak o_v)$.

Source: Voight 2021, Lemma 10.4.3 and Cor. 10.5.5. -/
@[kb "voight2021" "Cor. 10.5.5; Lemma 10.4.3"]
theorem exists_algEquiv_localOrder_eq_matOrder_nf {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsMaximalOrder (𝓞 F) F O) (hsplit : Nonempty (QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv)) :
    ∃ φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv,
      (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) = matOrder 𝔬 Fv := by
  obtain ⟨φ₀⟩ := hsplit
  have hM := (isMaximalOrder_localOrder_nf (v := v) hO).map φ₀
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := exists_eq_conj_matOrder hM
  refine ⟨φ₀.trans (conjAlgEquiv P Q hPQ hQP).symm, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : φ₀ x ∈ (localOrder (v := v) a b O).map ((φ₀ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) :=
      ⟨x, hx, rfl⟩
    rw [hconj] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    have : (conjAlgEquiv P Q hPQ hQP).symm (φ₀ x) = z := by
      rw [← hzx]; exact (conjAlgEquiv P Q hPQ hQP).symm_apply_apply z
    change (conjAlgEquiv P Q hPQ hQP).symm (φ₀ x) ∈ matOrder 𝔬 Fv
    rw [this]; exact hz
  · intro hy
    have h1 : conjAlgEquiv P Q hPQ hQP y ∈
        (localOrder (v := v) a b O).map ((φ₀ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) := by
      rw [hconj]; exact ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h1
    refine ⟨x, hx, ?_⟩
    change (conjAlgEquiv P Q hPQ hQP).symm (φ₀ x) = y
    rw [show φ₀ x = conjAlgEquiv P Q hPQ hQP y from hxy]
    exact (conjAlgEquiv P Q hPQ hQP).symm_apply_apply y

/-- **Local structure of a maximal order** ($\mathcal O_F$ a PID, $ab \ne 0$): at every finite place either $D_v$ is a division
algebra and $\mathcal O_v$ is its valuation ring, or $D_v \cong M_2(F_v)$ by an isomorphism carrying $\mathcal O_v$ onto
$M_2(\mathfrak o_v)$.

Source: Voight 2021, Lemma 10.4.3, Prop. 13.3.4, Cor. 10.5.5; Weil 1982, §3.7(a) (split or ramified). -/
@[kb "voight2021" "Lemma 10.4.3; Prop. 13.3.4; Cor. 10.5.5"]
theorem localOrder_ramified_or_split_nf (ha : a ≠ 0) (hb : b ≠ 0) {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsMaximalOrder (𝓞 F) F O) :
    (∃ hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0, localOrder (v := v) a b O = valOrder (R := 𝔬) hdiv) ∨
      ∃ φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv,
        (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) = matOrder 𝔬 Fv := by
  by_cases h : ∃ x : QuatV v a b, x ≠ 0 ∧ nrd x = 0
  · right
    have ha' : algebraMap 𝔬 Fv (ι v a) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha)
    have hb' : algebraMap 𝔬 Fv (ι v b) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v hb)
    have h2 := two_ne_zero_of_algebra (F := F) Fv
    exact exists_algEquiv_localOrder_eq_matOrder_nf hO ((nonempty_algEquiv_matrix_iff h2 ha' hb').2
      ((hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 ha' hb').2 h))
  · left
    push Not at h
    have hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0 := fun x hx => by
      by_contra h0; exact h x h0 hx
    exact ⟨hdiv, localOrder_eq_valOrder_nf ha hb hO hdiv⟩

end LocalStructure

end QuadFormsKB.QuatOrder
