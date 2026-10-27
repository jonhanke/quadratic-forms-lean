import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeQuat
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Approx
/-!
# Place-by-place base change for finite adeles
For a finite extension $K/k$ of number fields, the idempotents $e_v\in\mathbb A_{k,f}$ ($1$ at $v$, $0$ elsewhere) are
sent by $\iota_f$ (`finMap`) to the idempotents of $\mathbb A_{K,f}$ supported exactly at the places $w\mid v$
(`finMap_eAdele_apply`). This gives, with the $\mathbb A_{k,f}$-linearity of the global base change, the local
decomposition $K\otimes_kk_v\cong\prod_{w\mid v}K_w$ without any valuation comparison $K_w/k_v$ (the idempotent route).

*Mathlib doing heavy lifting* (cited, not reproved): `IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem`,
`valuedAdicCompletion_eq_valuation'`, `mem_integers_of_valuation_le_one`, `RestrictedProduct.isOpen_forall_mem`,
`Valued.isOpen_ball`, `Ideal.eq_bot_of_under_eq_bot` (going-up for integral extensions). The FLT project's
`IsDedekindDomain.FiniteAdeleRing.baseChangeAlgEquiv` (`FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean`) proves
the same local decomposition by completing valuations; it is cited, not imported.
-/

open IsDedekindDomain NumberField Topology Filter
namespace QuadFormsKB.Tamagawa.Measure.Weil
noncomputable section
section
variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
local notation "Ak" => FiniteAdeleRing (𝓞 k) k
local notation "AK" => FiniteAdeleRing (𝓞 K) K

theorem isOpen_valued_lt_one {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    IsOpen {z : w.adicCompletion F | Valued.v z < 1} := by
  have := Valued.isOpen_ball (w.adicCompletion F) (1 : (Valued.v : Valuation (w.adicCompletion F) _).ValueGroup₀)
  convert this using 2
  simp [Valuation.restrict_lt_iff_lt_embedding]

theorem isOpen_integral_adeles {F : Type} [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ u : HeightOneSpectrum (𝓞 F), a u ∈ u.adicCompletionIntegers F} := by
  have := RestrictedProduct.isOpen_forall_mem (R := fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
    (A := fun u => u.adicCompletionIntegers F) (fun u => ?_)
  · exact this
  · exact Valued.isOpen_valuationSubring _

/-- The place of `k` below a place `w` of `K`. -/
def underPlace (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 k) where
  asIdeal := w.asIdeal.under (𝓞 k)
  isPrime := inferInstance
  ne_bot := fun h => w.ne_bot (Ideal.eq_bot_of_under_eq_bot h)

open scoped algebraMap in
/-- The image of an integer `s ∈ 𝓞 k` in `𝔸_{k,f}`. -/
def intAdele (F : Type) [Field F] [NumberField F] : 𝓞 F →+* FiniteAdeleRing (𝓞 F) F :=
  (algebraMap F (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap (𝓞 F) F)

theorem intAdele_apply {F : Type} [Field F] [NumberField F] (s : 𝓞 F) (u : HeightOneSpectrum (𝓞 F)) :
    (intAdele F s) u = ((algebraMap (𝓞 F) F s : F) : u.adicCompletion F) := rfl

theorem valued_intAdele_lt_one {F : Type} [Field F] [NumberField F] (s : 𝓞 F) (u : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((intAdele F s) u) < 1 ↔ s ∈ u.asIdeal := by
  rw [intAdele_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact HeightOneSpectrum.valuation_lt_one_iff_mem u s


/-- **Integral approximation.** An open set containing an everywhere-integral finite adele contains `intAdele s` for some
`s ∈ 𝓞 k` (strong approximation: `k` is dense, and a rational point that is integral at every place is an integer). -/
theorem exists_intAdele_mem {F : Type} [Field F] [NumberField F] {N : Set (FiniteAdeleRing (𝓞 F) F)}
    (hN : IsOpen N) {a : FiniteAdeleRing (𝓞 F) F} (haN : a ∈ N)
    (ha : ∀ u : HeightOneSpectrum (𝓞 F), a u ∈ u.adicCompletionIntegers F) :
    ∃ s : 𝓞 F, intAdele F s ∈ N := by
  obtain ⟨x, hx⟩ := (denseRange_algebraMap_finiteAdele (F := F)).exists_mem_open
    (hN.inter isOpen_integral_adeles) ⟨a, haN, ha⟩
  have hint : x ∈ (algebraMap (𝓞 F) F).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun u => ?_
    have := hx.2 u
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) u = (x : u.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    exact this
  obtain ⟨s, rfl⟩ := hint
  exact ⟨s, hx.1⟩


theorem finMap_intAdele (s : 𝓞 k) :
    finMap k K (intAdele k s) = intAdele K (algebraMap (𝓞 k) (𝓞 K) s) := by
  unfold intAdele
  simp only [RingHom.comp_apply]
  rw [finMap_algebraMap]
  rfl

theorem valued_finMap_intAdele_lt_one (s : 𝓞 k) (w : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((finMap k K (intAdele k s)) w) < 1 ↔ s ∈ w.asIdeal.under (𝓞 k) := by
  rw [finMap_intAdele, valued_intAdele_lt_one]
  rfl

open Classical in
/-- The idempotent `e_v ∈ 𝔸_{k,f}`: `1` at `v`, `0` elsewhere. -/
def eAdele (v : HeightOneSpectrum (𝓞 k)) : Ak :=
  RestrictedProduct.single (fun u : HeightOneSpectrum (𝓞 k) => u.adicCompletionIntegers k) v 1

open Classical in
theorem eAdele_apply (v u : HeightOneSpectrum (𝓞 k)) :
    (eAdele v) u = if u = v then 1 else 0 := by
  change (Pi.single v (1 : v.adicCompletion k) : ∀ u : HeightOneSpectrum (𝓞 k), u.adicCompletion k) u = _
  by_cases h : u = v
  · subst h; simp
  · simp [h]

theorem eAdele_mul_self (v : HeightOneSpectrum (𝓞 k)) : eAdele v * eAdele v = eAdele v := by
  refine FiniteAdeleRing.ext k fun u => ?_
  show (eAdele v) u * (eAdele v) u = (eAdele v) u
  rw [eAdele_apply]
  split_ifs <;> simp


/-- The `u`-component ring homomorphism `𝔸_{F,f} → F_u`. -/
def evAdele {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →+* u.adicCompletion F :=
  RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F) u

theorem evAdele_apply {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (a : FiniteAdeleRing (𝓞 F) F) : evAdele u a = a u := rfl

theorem continuous_evAdele {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) :
    Continuous (evAdele (F := F) u) :=
  RestrictedProduct.continuous_eval (R := fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
    (A := fun u => u.adicCompletionIntegers F) u

theorem not_mem_of_sub_mem {F : Type} [CommRing F] {I : Ideal F} (hI : I ≠ ⊤) {s : F}
    (h1 : s ∈ I) (h2 : s - 1 ∈ I) : False :=
  hI ((Ideal.eq_top_iff_one I).mpr (by simpa using I.sub_mem h1 h2))

open Classical in
/-- **Places of `K` over `v` see exactly the idempotent `e_v`.** The `w`-component of `ι(e_v)` is `1` if `w` lies over `v`
and `0` otherwise (`ι = finMap`). Proof by density (strong approximation): `ι(e_v)_w` is an idempotent of the field `K_w`;
an approximating integer `s ∈ 𝓞 k` would lie in `w ∩ 𝓞 k` and `1 + w ∩ 𝓞 k` at once. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §14, proof of the Lemma, (14.3)–(14.6), p. 64; §10, (10.2), p. 57; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem finMap_eAdele_apply (v : HeightOneSpectrum (𝓞 k)) (w : HeightOneSpectrum (𝓞 K)) :
    (finMap k K (eAdele v)) w = if underPlace w = v then 1 else 0 := by
  classical
  set z := (finMap k K (eAdele v)) w with hz
  have hidem : z * z = z := by
    have := congrArg (evAdele w) (show finMap k K (eAdele v) * finMap k K (eAdele v) = finMap k K (eAdele v) by
      rw [← map_mul, eAdele_mul_self])
    rw [map_mul] at this
    exact this
  have h01 : z = 0 ∨ z = 1 := by
    by_cases h0 : z = 0
    · exact Or.inl h0
    · exact Or.inr (mul_left_cancel₀ h0 (by rw [mul_one]; exact hidem))
  have hfm : Continuous fun a : Ak => evAdele w (finMap k K a) :=
    (continuous_evAdele w).comp continuous_finMap
  have hint : ∀ u, (eAdele v) u ∈ u.adicCompletionIntegers k := by
    intro u
    rw [eAdele_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hne : w.asIdeal.under (𝓞 k) ≠ ⊤ := (Ideal.IsPrime.ne_top inferInstance)
  have hsub : ∀ s : 𝓞 k, intAdele k (s - 1) = intAdele k s - 1 := fun s => by simp
  by_cases hw : underPlace w = v
  · simp only [hw, ↓reduceIte]
    rcases h01 with h0 | h1
    · exfalso
      set N : Set Ak := {a | Valued.v (evAdele v a - 1) < 1} ∩ {a | Valued.v (evAdele w (finMap k K a)) < 1}
        with hN
      have hNo : IsOpen N :=
        ((isOpen_valued_lt_one v).preimage ((continuous_evAdele v).sub continuous_const)).inter
          ((isOpen_valued_lt_one w).preimage hfm)
      have heN : eAdele v ∈ N := by
        refine ⟨?_, ?_⟩
        · show Valued.v ((eAdele v) v - 1) < 1
          rw [eAdele_apply]; simp
        · show Valued.v z < 1
          rw [h0]; simp
      obtain ⟨s, hs⟩ := exists_intAdele_mem hNo heN hint
      have h1 : s - 1 ∈ v.asIdeal := by
        have : Valued.v (evAdele v (intAdele k s) - 1) < 1 := hs.1
        rw [← valued_intAdele_lt_one]
        change Valued.v (evAdele v (intAdele k (s - 1))) < 1
        rw [hsub, map_sub, map_one]
        exact this
      have h2 : s ∈ w.asIdeal.under (𝓞 k) := by
        rw [← valued_finMap_intAdele_lt_one (K := K)]
        exact hs.2
      have h3 : s - 1 ∈ w.asIdeal.under (𝓞 k) := by
        have : v.asIdeal = w.asIdeal.under (𝓞 k) := by rw [← hw]; rfl
        rwa [this] at h1
      exact not_mem_of_sub_mem hne h2 h3
    · exact h1
  · simp only [hw, ↓reduceIte]
    rcases h01 with h0 | h1
    · exact h0
    · exfalso
      set p := underPlace (k := k) w with hp
      set N : Set Ak := {a | Valued.v (evAdele p a) < 1} ∩ {a | Valued.v (evAdele w (finMap k K a) - 1) < 1}
        with hN
      have hNo : IsOpen N :=
        ((isOpen_valued_lt_one p).preimage (continuous_evAdele p)).inter
          ((isOpen_valued_lt_one w).preimage (hfm.sub continuous_const))
      have heN : eAdele v ∈ N := by
        refine ⟨?_, ?_⟩
        · show Valued.v ((eAdele v) p) < 1
          rw [eAdele_apply]; simp [hw]
        · show Valued.v (z - 1) < 1
          rw [h1]; simp
      obtain ⟨s, hs⟩ := exists_intAdele_mem hNo heN hint
      have h2 : s ∈ w.asIdeal.under (𝓞 k) := by
        have : Valued.v (evAdele p (intAdele k s)) < 1 := hs.1
        exact (valued_intAdele_lt_one s p).mp this
      have h3 : s - 1 ∈ w.asIdeal.under (𝓞 k) := by
        rw [← valued_finMap_intAdele_lt_one (K := K)]
        change Valued.v (evAdele w (finMap k K (intAdele k (s - 1)))) < 1
        rw [hsub]
        simp only [map_sub, map_one]
        exact hs.2
      exact not_mem_of_sub_mem hne h2 h3


open Classical in
/-- The embedding `k_v → 𝔸_{k,f}` into the `v`-th coordinate (`RestrictedProduct.single`), as an additive map. -/
def singleAdele (v : HeightOneSpectrum (𝓞 k)) : v.adicCompletion k →+ Ak :=
  RestrictedProduct.singleAddMonoidHom (fun u : HeightOneSpectrum (𝓞 k) => u.adicCompletionIntegers k) v

open Classical in
theorem singleAdele_apply_self (v : HeightOneSpectrum (𝓞 k)) (c : v.adicCompletion k) :
    (singleAdele v c) v = c := by
  change (Pi.single v c : ∀ u : HeightOneSpectrum (𝓞 k), u.adicCompletion k) v = c
  simp

open Classical in
theorem singleAdele_apply_ne {v u : HeightOneSpectrum (𝓞 k)} (h : u ≠ v) (c : v.adicCompletion k) :
    (singleAdele v c) u = 0 := by
  change (Pi.single v c : ∀ u : HeightOneSpectrum (𝓞 k), u.adicCompletion k) u = 0
  simp [h]

theorem eAdele_eq_singleAdele (v : HeightOneSpectrum (𝓞 k)) : eAdele v = singleAdele v 1 := rfl

/-- `e_v · a` is the adele supported at `v` with value `a_v`. -/
theorem eAdele_mul (v : HeightOneSpectrum (𝓞 k)) (a : Ak) : eAdele v * a = singleAdele v (a v) := by
  classical
  refine FiniteAdeleRing.ext k fun u => ?_
  show (eAdele v) u * a u = (singleAdele v (a v)) u
  by_cases h : u = v
  · subst h
    rw [singleAdele_apply_self, eAdele_eq_singleAdele, singleAdele_apply_self, one_mul]
  · rw [singleAdele_apply_ne h, eAdele_eq_singleAdele, singleAdele_apply_ne h, zero_mul]

theorem continuous_singleAdele (v : HeightOneSpectrum (𝓞 k)) : Continuous (singleAdele v) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 k)) := {v}ᶜ
  have hS : Filter.cofinite ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; simp [S]
  let g : v.adicCompletion k → RestrictedProduct (fun u : HeightOneSpectrum (𝓞 k) => u.adicCompletion k)
      (fun u => (u.adicCompletionIntegers k : Set (u.adicCompletion k))) (Filter.principal S) :=
    fun c => ⟨Pi.single v c, by
      rw [Filter.eventually_principal]
      intro u hu
      have : u ≠ v := hu
      simp [Pi.single_eq_of_ne this]⟩
  have hg : Continuous g := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_single v
  have := (RestrictedProduct.continuous_inclusion (R := fun u : HeightOneSpectrum (𝓞 k) => u.adicCompletion k)
    (A := fun u => (u.adicCompletionIntegers k : Set (u.adicCompletion k))) hS).comp hg
  exact this


theorem singleAdele_mul (v : HeightOneSpectrum (𝓞 k)) (c c' : v.adicCompletion k) :
    singleAdele v c * singleAdele v c' = singleAdele v (c * c') := by
  classical
  refine FiniteAdeleRing.ext k fun u => ?_
  show (singleAdele v c) u * (singleAdele v c') u = (singleAdele v (c * c')) u
  by_cases h : u = v
  · subst h; simp only [singleAdele_apply_self]
  · simp only [singleAdele_apply_ne h, zero_mul]

theorem eAdele_mul_single (v : HeightOneSpectrum (𝓞 k)) (c : v.adicCompletion k) :
    eAdele v * singleAdele v c = singleAdele v c := by
  rw [eAdele_mul, singleAdele_apply_self]

section Local

variable {ι : Type} [Fintype ι] (b : Module.Basis ι k K) (v : HeightOneSpectrum (𝓞 k))

/-- **The local base change** $K\otimes_kk_v\to\mathbb A_{K,f}$ in the coordinates $b$: $c\mapsto\Psi_f(c e_v)$,
i.e. $\sum_ic_ib_i$ with $c_i\in k_v\subset\mathbb A_{k,f}$ placed at $v$. -/
def localBaseChange : (ι → v.adicCompletion k) → AK := fun c => finBaseChange b fun i => singleAdele v (c i)

theorem localBaseChange_eq_sum (c : ι → v.adicCompletion k) :
    localBaseChange b v c = ∑ i, algebraMap K AK (b i) * finMap k K (singleAdele v (c i)) :=
  finBaseChange_eq_sum b _

theorem localBaseChange_add (c c' : ι → v.adicCompletion k) :
    localBaseChange b v (c + c') = localBaseChange b v c + localBaseChange b v c' := by
  simp only [localBaseChange, Pi.add_apply, map_add]
  exact map_add (finBaseChange b) _ _

theorem continuous_localBaseChange : Continuous (localBaseChange b v) :=
  (finBaseChange b).continuous.comp (continuous_pi fun i => (continuous_singleAdele v).comp (continuous_apply i))

/-- **$\mathbb A_{k,f}$-linearity of $\Psi_f$**: $\iota(t)\Psi_f(a) = \Psi_f(ta)$. -/
theorem finMap_mul_finBaseChange (t : Ak) (a : ι → Ak) :
    finMap k K t * finBaseChange b a = finBaseChange b fun i => t * a i := by
  rw [finBaseChange_eq_sum, finBaseChange_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]; ring

theorem finMap_mul_localBaseChange (t : Ak) (c : ι → v.adicCompletion k) :
    finMap k K t * localBaseChange b v c = finBaseChange b fun i => t * singleAdele v (c i) :=
  finMap_mul_finBaseChange b t _

theorem eAdele_smul_localBaseChange (c : ι → v.adicCompletion k) :
    finMap k K (eAdele v) * localBaseChange b v c = localBaseChange b v c := by
  rw [finMap_mul_localBaseChange]
  simp only [localBaseChange, eAdele_mul_single]

/-- **Range of the local base change.** $\Psi_f(c e_v)$ ranges exactly over the $y\in\mathbb A_{K,f}$ with
$\iota(e_v)y = y$, i.e. (by `finMap_eAdele_apply`) over the adeles supported at the places over $v$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §14, proof of the Lemma, (14.3)–(14.6), p. 64; §10, (10.2), p. 57; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem range_localBaseChange :
    Set.range (localBaseChange b v) = {y : AK | finMap k K (eAdele v) * y = y} := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    exact eAdele_smul_localBaseChange b v c
  · intro hy
    obtain ⟨a, rfl⟩ := (finBaseChange b).surjective y
    refine ⟨fun i => a i v, ?_⟩
    have h : finMap k K (eAdele v) * finBaseChange b a = finBaseChange b a := hy
    rw [finMap_mul_finBaseChange] at h
    rw [← h]
    simp only [localBaseChange, eAdele_mul]

/-- The local base change is injective, continuous and a homeomorphism onto its range: the topological identification of
$K\otimes_kk_v$ with the closed subgroup of $\mathbb A_{K,f}$ of adeles supported over $v$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §10, Thm., (10.2), p. 57 (algebraically and topologically); §14, proof of the Lemma, p. 64; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem isEmbedding_localBaseChange : Topology.IsEmbedding (localBaseChange b v) := by
  classical
  let g : (ι → v.adicCompletion k) → (ι → Ak) := fun c i => singleAdele v (c i)
  let f : (ι → Ak) → (ι → v.adicCompletion k) := fun a i => a i v
  have hfg : Function.LeftInverse f g := fun c => funext fun i => singleAdele_apply_self v (c i)
  have hg : Topology.IsEmbedding g :=
    hfg.isEmbedding (continuous_pi fun i => (continuous_evAdele v).comp (continuous_apply i))
      (continuous_pi fun i => (continuous_singleAdele v).comp (continuous_apply i))
  exact (finBaseChange b).toHomeomorph.isEmbedding.comp hg



theorem evAdele_finMap_mul (t y : AK) (w : HeightOneSpectrum (𝓞 K)) :
    (t * y) w = t w * y w := rfl

open Classical in
/-- **Support characterisation.** $y\in\mathbb A_{K,f}$ is in the image of $K\otimes_kk_v$ iff its components at the
places $w$ not over $v$ vanish. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §14, proof of the Lemma, (14.3)–(14.6), p. 64; §10, (10.2), p. 57; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem mem_range_localBaseChange_iff (y : AK) :
    y ∈ Set.range (localBaseChange b v) ↔ ∀ w : HeightOneSpectrum (𝓞 K), underPlace (k := k) w ≠ v → y w = 0 := by
  rw [range_localBaseChange]
  show finMap k K (eAdele v) * y = y ↔ _
  constructor
  · intro h w hw
    have h1 : (finMap k K (eAdele v) * y) w = y w := by rw [h]
    rw [evAdele_finMap_mul, finMap_eAdele_apply, if_neg hw, zero_mul] at h1
    exact h1.symm
  · intro h
    refine FiniteAdeleRing.ext K fun w => ?_
    rw [evAdele_finMap_mul, finMap_eAdele_apply]
    by_cases hw : underPlace w = v
    · rw [if_pos hw, one_mul]
    · rw [if_neg hw, zero_mul, h w hw]

/-- **The local ring maps $k_v\to K_w$ for $w\mid v$** (`w` lies over `v`): $c\mapsto\iota(c\,e_v)_w$. It is the
unique continuous ring homomorphism extending $k\to K\to K_w$ (not proved; not needed). -/
def localRingHom (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) :
    v.adicCompletion k →+* w.adicCompletion K where
  toFun c := (finMap k K (singleAdele v c)) w
  map_one' := by
    classical
    have := finMap_eAdele_apply (k := k) (K := K) v w
    rw [if_pos h] at this
    exact this
  map_mul' c c' := by
    show (finMap k K (singleAdele v (c * c'))) w =
      (finMap k K (singleAdele v c)) w * (finMap k K (singleAdele v c')) w
    rw [← singleAdele_mul, map_mul]; rfl
  map_zero' := by simp [map_zero]; rfl
  map_add' c c' := by
    show (finMap k K (singleAdele v (c + c'))) w =
      (finMap k K (singleAdele v c)) w + (finMap k K (singleAdele v c')) w
    rw [map_add, map_add]; rfl

theorem continuous_localRingHom (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) :
    Continuous (localRingHom v w h) :=
  (continuous_evAdele w).comp (continuous_finMap.comp (continuous_singleAdele v))

/-- **The $v$-component of the global base change is the local map** (additive level):
for $w\mid v$, $\Psi(ce_v)_w = \sum_ib_i\,\varphi_w(c_i)$ with $\varphi_w$ = `localRingHom`. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §14, proof of the Lemma, (14.3)–(14.6), p. 64; §10, (10.2), p. 57; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem localBaseChange_apply_over (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v)
    (c : ι → v.adicCompletion k) :
    (localBaseChange b v c) w = ∑ i, ((b i : K) : w.adicCompletion K) * localRingHom v w h (c i) := by
  rw [localBaseChange_eq_sum]
  show evAdele w _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  rfl

theorem localBaseChange_apply_ne (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w ≠ v)
    (c : ι → v.adicCompletion k) : (localBaseChange b v c) w = 0 :=
  (mem_range_localBaseChange_iff b v _).mp ⟨c, rfl⟩ w h

/-- **The $w$-component of $\iota_f$ factors through the $v$-component** ($w\mid v$):
$\iota_f(a)_w = \varphi_w(a_v)$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §14, proof of the Lemma, (14.3)–(14.6), p. 64; §10, (10.2), p. 57; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem finMap_apply_over (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) (a : Ak) :
    (finMap k K a) w = localRingHom v w h (a v) := by
  classical
  have h1 : (finMap k K (eAdele v)) w = 1 := by
    have := finMap_eAdele_apply (k := k) (K := K) v w
    rwa [if_pos h] at this
  have h2 : (finMap k K (eAdele v * a)) w = (finMap k K a) w := by
    rw [map_mul, evAdele_finMap_mul, h1, one_mul]
  rw [← h2, eAdele_mul]
  rfl

/-- $\varphi_w$ extends $k\to K\to K_w$: it sends $c\in k\subset k_v$ to $c\in K\subset K_w$. -/
theorem localRingHom_algebraMap (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) (c : k) :
    localRingHom v w h (c : v.adicCompletion k) = ((algebraMap k K c : K) : w.adicCompletion K) := by
  have := finMap_apply_over v w h (algebraMap k Ak c)
  rw [finMap_algebraMap] at this
  exact this.symm

/-- **$v$-components of $\iota_f(a)$** for all $w$ at once: $\iota_f(a)_w = \varphi_w(a_v)$ for $w\mid v$. This is the
compatibility of the global map $\iota$ (`adeleMap`) with the local maps. -/
theorem adeleMap_snd_apply_over (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) (a : Adeles k) :
    ((adeleMap k K a).2) w = localRingHom v w h (a.2 v) :=
  finMap_apply_over v w h a.2

end Local

section Quadratic

variable {d : k} {b : Module.Basis (Fin 2) k K} (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap k K d)
  (v : HeightOneSpectrum (𝓞 k))

/-- **The local quadratic map** $E\otimes_kk_v = k_v[\omega]/(\omega^2 - d)\to K_w$, $x + y\omega\mapsto\varphi_w(x) +
\delta\varphi_w(y)$, for $w\mid v$. -/
def quadLocalHom (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) :
    QuadraticAlgebra (v.adicCompletion k) (d : v.adicCompletion k) 0 →+* w.adicCompletion K where
  toFun z := localRingHom v w h z.re + ((b 1 : K) : w.adicCompletion K) * localRingHom v w h z.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_zero' := by simp
  map_add' z z' := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring
  map_mul' z z' := by
    have hδ : ((b 1 : K) : w.adicCompletion K) * ((b 1 : K) : w.adicCompletion K) =
        localRingHom v w h (d : v.adicCompletion k) := by
      rw [localRingHom_algebraMap, ← hb1]
      exact (map_mul (FinitePlace.embedding w) (b 1) (b 1)).symm
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, zero_mul, add_zero,
      map_zero]
    linear_combination (-(localRingHom v w h z.im * localRingHom v w h z'.im)) * hδ

/-- **The local quadratic base change** $E\otimes_kk_v\to\mathbb A_{K,f}$, $x + y\omega\mapsto\Psi_f((x,y)e_v)$. -/
def quadLocalBaseChange (z : QuadraticAlgebra (v.adicCompletion k) (d : v.adicCompletion k) 0) : AK :=
  localBaseChange b v ![z.re, z.im]

include hb0 in
/-- **Local decomposition, quadratic case (components).** For $w\mid v$ the $w$-component of the local base change is the
ring homomorphism `quadLocalHom`; for $w\nmid v$ it vanishes. So `quadLocalBaseChange` is the map
$E\otimes_kk_v\to\prod_{w\mid v}K_w$ with components `quadLocalHom`. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §14, proof of the Lemma, (14.3)–(14.6), p. 64; §10, (10.2), p. 57; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem quadLocalBaseChange_apply_over (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v)
    (z : QuadraticAlgebra (v.adicCompletion k) (d : v.adicCompletion k) 0) :
    (quadLocalBaseChange v (b := b) z) w = quadLocalHom hb1 v w h z := by
  unfold quadLocalBaseChange
  have h1 : ((1 : K) : w.adicCompletion K) = 1 := map_one (FinitePlace.embedding w)
  rw [localBaseChange_apply_over b v w h, Fin.sum_univ_two]
  simp only [quadLocalHom, hb0, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [h1, one_mul]

theorem quadLocalBaseChange_apply_ne (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w ≠ v)
    (z : QuadraticAlgebra (v.adicCompletion k) (d : v.adicCompletion k) 0) :
    (quadLocalBaseChange v (b := b) z) w = 0 :=
  localBaseChange_apply_ne b v w h _

/-- **Compatibility with the global `quadBaseChange`**: for $w\mid v$, the $w$-component of
$\Theta(z)$ is `quadLocalHom` applied to the $v$-components of $z$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §14, proof of the Lemma, (14.3)–(14.6), p. 64; §10, (10.2), p. 57; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem quadBaseChange_snd_apply_over (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v)
    (z : QuadAdele k d) :
    ((quadBaseChange hb0 hb1 z).2) w =
      quadLocalHom hb1 v w h ⟨z.re.2 v, z.im.2 v⟩ := by
  rw [quadBaseChange_apply]
  show (finMap k K z.re.2 + algebraMap K AK (b 1) * finMap k K z.im.2) w = _
  show (finMap k K z.re.2) w + ((algebraMap K AK (b 1)) w) * (finMap k K z.im.2) w = _
  rw [finMap_apply_over v w h, finMap_apply_over v w h]
  rfl

/-- **Range of the local quadratic base change**: exactly the adeles supported over $v$. (Topologically, the map is
an embedding for the coordinate topology $(x,y)\in k_v^2$ by `isEmbedding_localBaseChange`.) -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §14, proof of the Lemma, (14.3)–(14.6), p. 64; §10, (10.2), p. 57; FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem range_quadLocalBaseChange :
    Set.range (quadLocalBaseChange v (b := b) (d := d)) =
      {y : AK | ∀ w, underPlace (k := k) w ≠ v → y w = 0} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact (mem_range_localBaseChange_iff b v _).mp ⟨_, rfl⟩
  · intro hy
    obtain ⟨c, rfl⟩ := (mem_range_localBaseChange_iff b v y).mpr hy
    refine ⟨⟨c 0, c 1⟩, ?_⟩
    unfold quadLocalBaseChange
    congr 1
    funext i; fin_cases i <;> rfl

local notation "Ev" => QuadraticAlgebra (v.adicCompletion k) (d : v.adicCompletion k) 0

theorem quadLocalBaseChange_injective : Function.Injective (quadLocalBaseChange v (b := b) (d := d)) := by
  intro z z' h
  have h1 := (isEmbedding_localBaseChange b v).injective h
  refine QuadraticAlgebra.ext ?_ ?_
  · exact congrFun h1 0
  · exact congrFun h1 1

theorem quadLocalBaseChange_zero : quadLocalBaseChange v (b := b) (d := d) 0 = 0 := by
  unfold quadLocalBaseChange localBaseChange
  have : (fun i => singleAdele v (![(0 : Ev).re, (0 : Ev).im] i)) = 0 := by
    funext i; fin_cases i <;> simp
  rw [this]; exact map_zero (finBaseChange b)

include hb0 hb1 in
theorem quadLocalBaseChange_mul (z z' : Ev) (w : HeightOneSpectrum (𝓞 K)) :
    (quadLocalBaseChange v (b := b) (z * z')) w = (quadLocalBaseChange v (b := b) z) w *
      (quadLocalBaseChange v (b := b) z') w := by
  by_cases h : underPlace (k := k) w = v
  · rw [quadLocalBaseChange_apply_over hb0 hb1 v w h, quadLocalBaseChange_apply_over hb0 hb1 v w h,
      quadLocalBaseChange_apply_over hb0 hb1 v w h, map_mul]
  · rw [quadLocalBaseChange_apply_ne v w h, quadLocalBaseChange_apply_ne v w h, zero_mul]

include hb0 hb1 in
theorem quadLocalBaseChange_sub (z z' : Ev) (w : HeightOneSpectrum (𝓞 K)) :
    (quadLocalBaseChange v (b := b) (z - z')) w = (quadLocalBaseChange v (b := b) z) w -
      (quadLocalBaseChange v (b := b) z') w := by
  by_cases h : underPlace (k := k) w = v
  · rw [quadLocalBaseChange_apply_over hb0 hb1 v w h, quadLocalBaseChange_apply_over hb0 hb1 v w h,
      quadLocalBaseChange_apply_over hb0 hb1 v w h, map_sub]
  · rw [quadLocalBaseChange_apply_ne v w h, quadLocalBaseChange_apply_ne v w h,
      quadLocalBaseChange_apply_ne v w h, sub_zero]

include hb0 hb1 in
theorem quadLocalBaseChange_one_apply (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) :
    (quadLocalBaseChange v (b := b) (1 : Ev)) w = 1 := by
  rw [quadLocalBaseChange_apply_over hb0 hb1 v w h, map_one]

include hb0 hb1 in
/-- Every place $v$ of $k$ has a place $w$ of $K$ over it. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §10, Thm., (10.2), p. 57 (J ≥ 1 since k_v ⊗ K ≠ 0); FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem exists_place_over : ∃ w : HeightOneSpectrum (𝓞 K), underPlace (k := k) w = v := by
  by_contra hne
  push_neg at hne
  have h1 : quadLocalBaseChange v (b := b) (d := d) 1 = quadLocalBaseChange v (b := b) (d := d) 0 := by
    rw [quadLocalBaseChange_zero]
    refine FiniteAdeleRing.ext K fun w => ?_
    rw [quadLocalBaseChange_apply_ne v w (hne w)]; rfl
  exact one_ne_zero (quadLocalBaseChange_injective v h1)

include hb0 hb1 in
/-- **Split case: two places.** If $d$ is a nonzero square in $k_v$, there are two distinct places of $K$ over $v$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §10, Cor., p. 58 (the places over v correspond to the irreducible factors over k_v of the minimal polynomial); FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem exists_two_places_of_sq (c : v.adicCompletion k) (hc : c ≠ 0) (hd : (d : v.adicCompletion k) = c * c) :
    ∃ w₁ w₂ : HeightOneSpectrum (𝓞 K), w₁ ≠ w₂ ∧ underPlace (k := k) w₁ = v ∧ underPlace (k := k) w₂ = v := by
  have h2 : (2 : v.adicCompletion k) ≠ 0 := two_ne_zero
  let f : Ev := ⟨2⁻¹, 2⁻¹ * c⁻¹⟩
  have hff : f * f = f := by
    refine QuadraticAlgebra.ext ?_ ?_
    · simp only [f, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, add_zero, hd]
      field_simp; ring
    · simp only [f, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, add_zero]
      field_simp; ring
  have hf0 : f ≠ 0 := fun h => by
    have := congrArg QuadraticAlgebra.re h
    simp [f] at this
  have hf1 : 1 - f ≠ 0 := fun h => by
    have := congrArg QuadraticAlgebra.re h
    simp only [f, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_one, QuadraticAlgebra.re_zero] at this
    have h4 : (2⁻¹ : v.adicCompletion k) = 1 := by linear_combination -this
    have h5 : (2 : v.adicCompletion k) = 1 := inv_eq_one.mp h4
    norm_num at h5
  -- a place where `f` is nonzero, hence `1`
  have hex : ∀ g : Ev, g ≠ 0 → ∃ w, underPlace (k := k) w = v ∧ (quadLocalBaseChange v (b := b) g) w ≠ 0 := by
    intro g hg
    by_contra hcon
    push_neg at hcon
    apply hg
    apply quadLocalBaseChange_injective v (b := b)
    rw [quadLocalBaseChange_zero]
    refine FiniteAdeleRing.ext K fun w => ?_
    by_cases hw : underPlace (k := k) w = v
    · exact hcon w hw
    · rw [quadLocalBaseChange_apply_ne v w hw]; rfl
  obtain ⟨w₁, hw₁, hf₁⟩ := hex f hf0
  obtain ⟨w₂, hw₂, hf₂⟩ := hex (1 - f) hf1
  have hidem : ∀ w, (quadLocalBaseChange v (b := b) f) w * (quadLocalBaseChange v (b := b) f) w =
      (quadLocalBaseChange v (b := b) f) w := fun w => by
    rw [← quadLocalBaseChange_mul hb0 hb1, hff]
  refine ⟨w₁, w₂, fun heq => ?_, hw₁, hw₂⟩
  subst heq
  have h1 : (quadLocalBaseChange v (b := b) f) w₁ = 1 :=
    mul_left_cancel₀ hf₁ (by rw [mul_one]; exact hidem w₁)
  apply hf₂
  rw [quadLocalBaseChange_sub hb0 hb1, quadLocalBaseChange_one_apply hb0 hb1 v w₁ hw₁, h1, sub_self]

/-- In the nonsplit quadratic algebra $k_v[\omega]/(\omega^2 - d)$, the only idempotents are $0$ and $1$. -/
theorem idempotent_of_nonsq (hns : ∀ c : v.adicCompletion k, (d : v.adicCompletion k) ≠ c * c) (z : Ev)
    (hz : z * z = z) : z = 0 ∨ z = 1 := by
  have h2 : (2 : v.adicCompletion k) ≠ 0 := two_ne_zero
  have hre := congrArg QuadraticAlgebra.re hz
  have him := congrArg QuadraticAlgebra.im hz
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, add_zero] at hre him
  by_cases hy : z.im = 0
  · rw [hy] at hre
    have hx : z.re * (z.re - 1) = 0 := by linear_combination hre
    rcases mul_eq_zero.mp hx with h | h
    · left; exact QuadraticAlgebra.ext (by simpa using h) (by simpa using hy)
    · right
      exact QuadraticAlgebra.ext (by rw [QuadraticAlgebra.re_one]; linear_combination h)
        (by rw [QuadraticAlgebra.im_one]; exact hy)
  · exfalso
    have hx : z.re = 2⁻¹ := by
      field_simp
      apply mul_left_cancel₀ hy
      linear_combination him
    apply hns (2⁻¹ * z.im⁻¹)
    rw [hx] at hre
    field_simp
    field_simp at hre
    linear_combination hre

include hb0 hb1 in
/-- **Inert / ramified case: one place.** If $d$ is not a square in $k_v$, there is exactly one place of $K$ over $v$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §10, Cor., p. 58 (the places over v correspond to the irreducible factors over k_v of the minimal polynomial); FLT `FiniteAdeleRing.baseChangeAlgEquiv` (cited, not imported)"]
theorem place_unique_of_nonsq (hns : ∀ c : v.adicCompletion k, (d : v.adicCompletion k) ≠ c * c)
    (w₁ w₂ : HeightOneSpectrum (𝓞 K)) (h₁ : underPlace (k := k) w₁ = v) (h₂ : underPlace (k := k) w₂ = v) :
    w₁ = w₂ := by
  classical
  by_contra hne
  let y : AK := RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) w₁ 1
  have hy1 : y w₁ = 1 := by
    change (Pi.single w₁ (1 : w₁.adicCompletion K) : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) w₁ = 1
    simp
  have hy0 : ∀ w, w ≠ w₁ → y w = 0 := fun w hw => by
    change (Pi.single w₁ (1 : w₁.adicCompletion K) : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) w = 0
    simp [hw]
  have hsupp : y ∈ Set.range (quadLocalBaseChange v (b := b) (d := d)) := by
    rw [range_quadLocalBaseChange]
    intro w hw
    exact hy0 w fun h => hw (h ▸ h₁)
  obtain ⟨z, hz⟩ := hsupp
  have hzz : z * z = z := by
    apply quadLocalBaseChange_injective v (b := b)
    refine FiniteAdeleRing.ext K fun w => ?_
    rw [quadLocalBaseChange_mul hb0 hb1, hz]
    show y w * y w = y w
    by_cases hw : w = w₁
    · subst hw; rw [hy1, one_mul]
    · rw [hy0 w hw, zero_mul]
  rcases idempotent_of_nonsq v hns z hzz with h | h
  · subst h
    rw [quadLocalBaseChange_zero] at hz
    have := congrArg (fun a : AK => a w₁) hz
    rw [hy1] at this
    exact one_ne_zero this.symm
  · subst h
    have := congrArg (fun a : AK => a w₂) hz
    rw [quadLocalBaseChange_one_apply hb0 hb1 v w₂ h₂, hy0 w₂ (Ne.symm hne)] at this
    exact one_ne_zero this

end Quadratic

end
