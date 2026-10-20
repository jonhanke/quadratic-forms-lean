import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeLocal
import QuadFormsKB.Analysis.TraceLocalGlobal

/-!
# Local traces $\operatorname{Tr}_{K_w/k_v}$ and $\psi_{K,w}=\psi_{k,v}\circ\operatorname{Tr}_{K_w/k_v}$

For finite $K/k$ of number fields, a finite place $v$ of $k$ and a place $w\mid v$ of $K$ (`underPlace w = v`):

* `finite_placesOver`: only finitely many $w$ lie over $v$ (Mathlib `Algebra.QuasiFinite.finite_primesOver`);
  `placesOver v` is the resulting `Finset`.
* `localAlg v w h : Algebra k_v K_w` (through the library's `localRingHom`), `localTrace v w h` its trace
  $\operatorname{Tr}_{K_w/k_v}$.
* `resChar_eq_of_underPlace`: $w$ and $v$ have the same residue characteristic.
* **`psiV_eq_psiV_localTrace`**: $\psi_{K,w}(y)=\psi_{k,v}(\operatorname{Tr}_{K_w/k_v}y)$ for all $y\in K_w$ (the library's local
  characters `Analysis.psiV`), by transitivity of the trace along $\mathbb{Q}_p\subset k_v\subset K_w$; the tower is
  proved from continuity and density of $\mathbb{Q}$.

Sources: Neukirch, *Algebraic Number Theory*, Ch. II (8.3, 8.4) and Ch. VII §5 (the local-global trace) [unverified];
Cassels–Fröhlich Ch. II §14 [unverified]; Mathlib `Algebra.trace_trace`, `Algebra.QuasiFinite.finite_primesOver`.
-/

open IsDedekindDomain NumberField Topology Filter

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (v : HeightOneSpectrum (𝓞 k))

/-- Only finitely many places of $K$ lie over $v$. -/
theorem finite_placesOver : {w : HeightOneSpectrum (𝓞 K) | underPlace (k := k) w = v}.Finite := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := 𝓞 k) (S := 𝓞 K) v.asIdeal
  refine (hfin.preimage (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) ?_).subset ?_
  · intro a _ b _ hab; exact HeightOneSpectrum.ext hab
  · intro w hw
    refine ⟨w.isPrime, ⟨?_⟩⟩
    have : w.asIdeal.under (𝓞 k) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal hw
    exact this.symm

open Classical in
/-- The finite set of places of $K$ over $v$. -/
def placesOver : Finset (HeightOneSpectrum (𝓞 K)) := (finite_placesOver (K := K) v).toFinset

theorem mem_placesOver {w : HeightOneSpectrum (𝓞 K)} :
    w ∈ placesOver (K := K) v ↔ underPlace (k := k) w = v := by
  classical
  simp [placesOver]

/-- $w$ and the place of $k$ below it have the same residue characteristic. -/
theorem resChar_eq_of_underPlace (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) :
    Analysis.resChar w = Analysis.resChar v := by
  have hv : Analysis.vUnder w = Analysis.vUnder v := by
    refine HeightOneSpectrum.ext ?_
    show w.asIdeal.comap (algebraMap ℤ (𝓞 K)) = v.asIdeal.comap (algebraMap ℤ (𝓞 k))
    have : w.asIdeal.under (𝓞 k) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal h
    rw [← this]
    show _ = (w.asIdeal.comap (algebraMap (𝓞 k) (𝓞 K))).comap (algebraMap ℤ (𝓞 k))
    rw [Ideal.comap_comap]
    congr 1
    exact (RingHom.ext_int _ _)
  unfold Analysis.resChar
  rw [hv]


/-! ### The local algebra $K_w/k_v$ and the trace tower -/

/-- $K_w$ as a $k_v$-algebra via the library's `localRingHom` (given $w\mid v$). -/
@[instance_reducible]
def localAlg (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) :
    Algebra (v.adicCompletion k) (w.adicCompletion K) := (localRingHom v w h).toAlgebra

theorem algebraMap_localAlg (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) :
    @algebraMap _ _ _ _ (localAlg v w h) = localRingHom v w h := rfl

/-- The places of $K$ over $v$, as `Analysis.Sp K p` with $p$ = `resChar v` (for the $\mathbb{Q}_p$-algebra structure). -/
def toSp (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) : Analysis.Sp K (Analysis.resChar v) :=
  ⟨w, resChar_eq_of_underPlace v w h⟩

theorem denseRange_ratCast_padic (p : ℕ) [Fact p.Prime] : DenseRange (Rat.cast : ℚ → ℚ_[p]) := by
  refine Metric.denseRange_iff.mpr fun x r hr => ?_
  obtain ⟨q, hq⟩ := Padic.rat_dense p x hr
  exact ⟨q, by rw [dist_eq_norm]; exact hq⟩

theorem algebraMap_comp_localRingHom (w : Analysis.Sp K (Analysis.resChar v)) (h : underPlace (k := k) w.1 = v) :
    (localRingHom v w.1 h).comp (Analysis.padicToV v) =
      (algebraMap (ℚ_[Analysis.resChar v]) (Analysis.FvQ (Analysis.resChar v) w)) := by
  have hc1 : Continuous ((localRingHom v w.1 h).comp (Analysis.padicToV v)) :=
    (continuous_localRingHom v w.1 h).comp (Analysis.continuous_padicToV v)
  have hc2 : Continuous (algebraMap (ℚ_[Analysis.resChar v]) (Analysis.FvQ (Analysis.resChar v) w)) := by
    rw [show algebraMap (ℚ_[Analysis.resChar v]) (Analysis.FvQ (Analysis.resChar v) w) =
      (Analysis.padicToV w.1).comp (Analysis.padicCast w.2.symm).toRingHom from rfl]
    exact (Analysis.continuous_padicToV w.1).comp (Analysis.continuous_padicCast _)
  refine DFunLike.ext' ?_
  refine hc1.ext_on (denseRange_ratCast_padic (Analysis.resChar v)) hc2 ?_
  rintro _ ⟨r, rfl⟩
  haveI := RingHom.ext_rat ((localRingHom v w.1 h).comp (Analysis.padicToV v) |>.comp (Rat.castHom _))
    ((algebraMap (ℚ_[Analysis.resChar v]) (Analysis.FvQ (Analysis.resChar v) w)).comp (Rat.castHom _))
  exact congrArg (fun f => f r) this

/-- The `Fact`-wrapped algebra instance (so the lemmas can use typeclass inference). -/
instance instAlgebraLocal (w : HeightOneSpectrum (𝓞 K)) [h : Fact (underPlace (k := k) w = v)] :
    Algebra (v.adicCompletion k) (w.adicCompletion K) := localAlg v w h.out

theorem algebraMap_instAlgebraLocal (w : HeightOneSpectrum (𝓞 K)) [h : Fact (underPlace (k := k) w = v)] :
    algebraMap (v.adicCompletion k) (w.adicCompletion K) = localRingHom v w h.out := rfl

/-- **The local trace** $\operatorname{Tr}_{K_w/k_v}:K_w\to k_v$ ($w\mid v$), for the algebra structure `localAlg`. -/
@[kb "casselsfrohlich1967" "Ch. II §14 / Ch. XV §2.2, local trace [unverified]; Neukirch II.8 [unverified]"]
def localTrace (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := k) w = v) :
    (letI := localAlg v w h; w.adicCompletion K →ₗ[v.adicCompletion k] v.adicCompletion k) :=
  letI := localAlg v w h
  Algebra.trace (v.adicCompletion k) (w.adicCompletion K)

theorem finiteDimensional_localAlg (w : Analysis.Sp K (Analysis.resChar v)) (h : underPlace (k := k) w.1 = v) :
    letI := localAlg v w.1 h
    FiniteDimensional (v.adicCompletion k) (w.1.adicCompletion K) := by
  letI := localAlg v w.1 h
  haveI : IsScalarTower ℚ_[Analysis.resChar v] (v.adicCompletion k) (w.1.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      have := DFunLike.congr_fun (algebraMap_comp_localRingHom v w h) c
      exact this.symm
  haveI : FiniteDimensional ℚ_[Analysis.resChar v] (Analysis.FvQ (Analysis.resChar v) w) := inferInstance
  exact FiniteDimensional.right ℚ_[Analysis.resChar v] (v.adicCompletion k) (w.1.adicCompletion K)

theorem psiV_eq_psiP_trace_FvQ (q : ℕ) [Fact q.Prime] (w : Analysis.Sp K q) (y : w.1.adicCompletion K) :
    Analysis.psiV w.1 y = Analysis.psiP (p := q) (Algebra.trace ℚ_[q] (Analysis.FvQ q w) y) := by
  obtain ⟨w, hw⟩ := w
  subst hw
  rfl

/-- **$\psi_{K,w}=\psi_{k,v}\circ\operatorname{Tr}_{K_w/k_v}$** (local character compatibility). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 (ψ_w = ψ_v ∘ Tr_{K_w/k_v}); Neukirch II.8 [unverified]"]
theorem psiV_localTrace (w : Analysis.Sp K (Analysis.resChar v)) (h : underPlace (k := k) w.1 = v)
    (y : w.1.adicCompletion K) :
    Analysis.psiV w.1 y = Analysis.psiV v (localTrace v w.1 h y) := by
  letI := localAlg v w.1 h
  haveI : IsScalarTower ℚ_[Analysis.resChar v] (v.adicCompletion k) (w.1.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      have := DFunLike.congr_fun (algebraMap_comp_localRingHom v w h) c
      exact this.symm
  haveI := finiteDimensional_localAlg v w h
  have h1 := psiV_eq_psiP_trace_FvQ (Analysis.resChar v) w y
  rw [h1]
  have h2 := Algebra.trace_trace (R := ℚ_[Analysis.resChar v]) (S := v.adicCompletion k)
    (T := w.1.adicCompletion K) y
  change _ = Analysis.psiP (p := Analysis.resChar v) (Analysis.traceV v (localTrace v w.1 h y))
  rw [← h2]
  rfl

end

end QuadFormsKB.Tamagawa.Measure.Weil
