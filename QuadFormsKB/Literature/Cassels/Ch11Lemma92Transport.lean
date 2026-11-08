/-
# Cassels, Chapter 11, proof of Lemma 9.2: from $\mathbb Z_p$-lattices to local lattices of the library

**Purpose.** The local lattices $\Gamma_p$ of Cassels' proof are constructed over $\mathbb Z_p$ (as $\mathbb Z_p$-spans of the columns of a
$3 \times 3$ matrix $C$ in the coordinates $W$); the gluing and the spinor norm groups of the library live over the completion
$\mathbb Q_v$ of $\mathbb Q$ at the place $v$ over $p$. This file transports them along `adicCompletion.padicEquiv`.

**Proves** (for $v$ a place, $p$ its prime, $\psi : \mathbb Q_p \to \mathbb Q_v$ the inverse of `padicEquiv`, $C \in M_3(\mathbb Z_p)$
with $\det C \ne 0$, and `tLat v C` $= \psi(C)\,\mathfrak o_v^3$):
* `tLat_le_std`, `tLat_isLattice`;
* `intVec_mem_tLat_iff`: an integer vector $z$ lies in `tLat v C` iff $z = C\eta$ for some $\eta \in \mathbb Z_p^3$;
* `exists_mem_tLat_of_rep`: a representation $h(C\eta) = c$ over $\mathbb Z_p$ gives one by `tLat v C`;
* `units_mem_tLat`: the hypotheses of `units_mem_of_scaled_values` from $\mathbb Z_p$-facts about $h \circ C$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92Local

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

open QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section Transport

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- The prime of the place `v`. -/
abbrev pOf : ℕ := ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)

instance factPOf : Fact (pOf v).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

theorem pOf_eq : pOf v = Rat.HeightOneSpectrum.natGenerator v := rfl

/-- $\psi : \mathbb Q_p \to \mathbb Q_v$, the inverse of Mathlib's `adicCompletion.padicEquiv`. -/
def ψ : ℚ_[pOf v] →+* v.adicCompletion ℚ :=
  ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm : ℚ_[pOf v] ≃A[ℚ] v.adicCompletion ℚ).toRingEquiv.toRingHom

theorem ψ_injective : Function.Injective (ψ v) :=
  ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm : ℚ_[pOf v] ≃A[ℚ] v.adicCompletion ℚ).injective

theorem padicEquiv_ψ (x : ℚ_[pOf v]) : Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (ψ v x) = x :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply x

theorem ψ_padicEquiv (y : v.adicCompletion ℚ) : ψ v (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v y) = y :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm_apply_apply y

/-- $\psi$ maps $\mathbb Z_p$ into $\mathfrak o_v$. -/
theorem valued_ψ_le_one (x : ℤ_[pOf v]) : Valued.v (ψ v x) ≤ 1 := by
  obtain ⟨y, hy, hyx⟩ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).2.2
    (show (x : ℚ_[pOf v]) ∈ PadicInt.subring (pOf v) from x.2)
  rw [← hyx, ψ_padicEquiv]
  exact hy

/-- An element of $\mathfrak o_v$ is the image of an element of $\mathbb Z_p$. -/
theorem exists_padicInt_of_valued_le_one {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1) :
    ∃ x : ℤ_[pOf v], ψ v x = y :=
  ⟨⟨Rat.HeightOneSpectrum.adicCompletion.padicEquiv v y,
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).1 hy⟩, ψ_padicEquiv v y⟩

/-- $\chi : \mathbb Z_p \to \mathfrak o_v \subseteq \mathbb Q_v$, the restriction of $\psi$. -/
def χ : ℤ_[pOf v] →+* v.adicCompletion ℚ := (ψ v).comp PadicInt.Coe.ringHom

theorem χ_apply (x : ℤ_[pOf v]) : χ v x = ψ v x := rfl

theorem χ_injective : Function.Injective (χ v) := fun x y h => Subtype.ext ((ψ_injective v) h)

/-- The matrix $\psi(C)$. -/
def tMat (C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) :=
  (χ v).mapMatrix C

theorem tMat_det (C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]) : (tMat v C).det = χ v C.det :=
  (RingHom.map_det (χ v) C).symm

theorem tMat_det_ne_zero {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0) : (tMat v C).det ≠ 0 := by
  rw [tMat_det]
  intro h0
  exact hC ((χ_injective v) (by rw [h0, map_zero]))

/-- $\psi(C)$ as an element of $\mathrm{GL}_3(\mathbb Q_v)$. -/
def tGL {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0) : GL (Fin 3) (v.adicCompletion ℚ) :=
  Matrix.nonsingInvUnit (tMat v C) (isUnit_iff_ne_zero.mpr (tMat_det_ne_zero v hC))

theorem tGL_val {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0) : (tGL v hC).val = tMat v C := rfl

/-- **The local lattice $\psi(C)\,\mathfrak o_v^3$.** -/
def tLat {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0) :
    Submodule (v.adicCompletionIntegers ℚ) (Fin 3 → v.adicCompletion ℚ) :=
  locAct v (tGL v hC) (std v)

theorem tLat_isLattice {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0) :
    (tLat v hC).IsLattice (v.adicCompletion ℚ) :=
  locAct_isLattice _ (isLattice_of_bounds v le_rfl le_rfl)

/-- Helper: $\psi(C)\chi(\eta) = \chi(C\eta)$. -/
theorem tMat_mulVec (C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]) (η : Fin 3 → ℤ_[pOf v]) :
    tMat v C *ᵥ (fun i => χ v (η i)) = fun i => χ v ((C *ᵥ η) i) := by
  funext i
  exact (RingHom.map_mulVec (χ v) C η i).symm

/-- **Membership in $\psi(C)\,\mathfrak o_v^3$:** $y \in$ `tLat v C` iff $y = \chi(C\eta)$ for some $\eta \in \mathbb Z_p^3$. -/
theorem mem_tLat_iff {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0) (y : Fin 3 → v.adicCompletion ℚ) :
    y ∈ tLat v hC ↔ ∃ η : Fin 3 → ℤ_[pOf v], y = fun i => χ v ((C *ᵥ η) i) := by
  rw [tLat, mem_locAct, tGL_val]
  constructor
  · rintro ⟨x, hx, rfl⟩
    choose η hη using fun i => exists_padicInt_of_valued_le_one v (hx i)
    refine ⟨η, ?_⟩
    rw [← tMat_mulVec]
    congr 1
    funext i; exact (hη i).symm
  · rintro ⟨η, rfl⟩
    refine ⟨fun i => χ v (η i), fun i => ?_, tMat_mulVec v C η⟩
    have := valued_ψ_le_one v (η i)
    rw [← χ_apply] at this
    simpa using this

theorem tLat_le_std {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0) : tLat v hC ≤ std v := by
  intro y hy
  obtain ⟨η, rfl⟩ := (mem_tLat_iff v hC y).mp hy
  intro i
  have := valued_ψ_le_one v ((C *ᵥ η) i)
  rw [← χ_apply] at this
  simpa using this

theorem χ_intCast (z : ℤ) : χ v (z : ℤ_[pOf v]) = algebraMap ℚ (v.adicCompletion ℚ) (z : ℚ) := by
  rw [map_intCast, map_intCast]

/-- **Integer vectors in $\psi(C)\,\mathfrak o_v^3$:** $z \in \mathbb Z^3$ lies in `tLat v C` iff $z = C\eta$ with $\eta \in \mathbb Z_p^3$. -/
theorem intVec_mem_tLat_iff {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0) (z : Fin 3 → ℤ) :
    locVec v (fun i => (z i : ℚ)) ∈ tLat v hC ↔ ∃ η : Fin 3 → ℤ_[pOf v], (fun i => (z i : ℤ_[pOf v])) = C *ᵥ η := by
  rw [mem_tLat_iff]
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨η, funext fun i => (χ_injective v) ?_⟩
    have := congrFun hη i
    simp only [locVec_apply] at this
    rw [χ_intCast, this]
  · rintro ⟨η, hη⟩
    refine ⟨η, funext fun i => ?_⟩
    simp only [locVec_apply]
    rw [← χ_intCast, ← hη]

/-- Helper: evaluation of an integer form commutes with $\chi$. -/
theorem evalIn_χ {m : ℕ} (h : QuadForm ℤ m) (x : Fin m → ℤ_[pOf v]) :
    (h.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (fun i => χ v (x i)) =
      χ v ((h.map (Int.castRingHom ℤ_[pOf v])).eval x) := by
  rw [evalIn_castHom_rat, hom_eval_castHom h (χ v) x]

/-- Helper: the polar form of an integer form commutes with $\chi$. -/
theorem qbil_χ {m : ℕ} (h : QuadForm ℤ m) (x y : Fin m → ℤ_[pOf v]) :
    qbil (h.map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) (fun i => χ v (x i)) (fun i => χ v (y i)) =
      χ v ((h.map (Int.castRingHom ℤ_[pOf v])).eval (x + y) - (h.map (Int.castRingHom ℤ_[pOf v])).eval x -
        (h.map (Int.castRingHom ℤ_[pOf v])).eval y) := by
  rw [map_sub, map_sub, ← evalIn_χ, ← evalIn_χ, ← evalIn_χ]
  simp only [qbil]
  rw [← QuadForm.polar_eq_hessian]
  congr 3
  funext i; simp [map_add]

/-- **Representations transport:** if $h(C\eta) = c$ over $\mathbb Z_p$, then $c$ is represented by `tLat v C`. -/
theorem exists_mem_tLat_of_rep (h : QuadForm ℤ 3) {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0)
    {c : ℤ} (hrep : ∃ η : Fin 3 → ℤ_[pOf v], (h.map (Int.castRingHom ℤ_[pOf v])).eval (C *ᵥ η) = c) :
    ∃ y ∈ tLat v hC, (h.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) y =
      algebraMap ℚ (v.adicCompletion ℚ) (c : ℚ) := by
  obtain ⟨η, hη⟩ := hrep
  refine ⟨fun i => χ v ((C *ᵥ η) i), (mem_tLat_iff v hC _).mpr ⟨η, rfl⟩, ?_⟩
  rw [evalIn_χ, hη, χ_intCast]

/-- **$U_p \subseteq \theta(\Gamma_p)$ from $\mathbb Z_p$-facts** (for `units_mem_of_scaled_values`): if every polar value
$B_h(C\eta, C\eta')$ is divisible by $p^\mu$ and every $p^\mu w$, $w \in \mathbb Z_p^\times$, is $h(C\eta)$, then every unit of
$\mathbb Q_v$ is in $\theta$ of any global lattice with localization `tLat v C` at $v$. -/
theorem units_mem_tLat (h : QuadForm ℤ 3) {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0) (μ : ℕ)
    (hbil : ∀ η η' : Fin 3 → ℤ_[pOf v], (pOf v : ℤ_[pOf v]) ^ μ ∣
      (h.map (Int.castRingHom ℤ_[pOf v])).eval (C *ᵥ η + C *ᵥ η') -
        (h.map (Int.castRingHom ℤ_[pOf v])).eval (C *ᵥ η) - (h.map (Int.castRingHom ℤ_[pOf v])).eval (C *ᵥ η'))
    (hval : ∀ w : ℤ_[pOf v], IsUnit w → ∃ η : Fin 3 → ℤ_[pOf v],
      (h.map (Int.castRingHom ℤ_[pOf v])).eval (C *ᵥ η) = (pOf v : ℤ_[pOf v]) ^ μ * w)
    (L : Lat ℚ 3) (hQ : (h.map (Int.castRingHom ℚ)).Nondegenerate) (hL : loc v L.1 = tLat v hC)
    (w : (v.adicCompletion ℚ)ˣ) (hw : Valued.v (w : v.adicCompletion ℚ) = 1) :
    w ∈ localSpinorNormGroup _ hQ v L := by
  have hπ0 : χ v ((pOf v : ℤ_[pOf v]) ^ μ) ≠ 0 := fun h0 =>
    pow_ne_zero μ (by exact_mod_cast (Fact.out : (pOf v).Prime).ne_zero : (pOf v : ℤ_[pOf v]) ≠ 0)
      ((χ_injective v) (by rw [h0, map_zero]))
  refine units_mem_of_scaled_values hQ L hπ0 ?_ ?_ w hw
  · intro x hx y hy
    rw [hL] at hx hy
    obtain ⟨η, rfl⟩ := (mem_tLat_iff v hC x).mp hx
    obtain ⟨η', rfl⟩ := (mem_tLat_iff v hC y).mp hy
    rw [qbil_χ]
    obtain ⟨t, ht⟩ := hbil η η'
    rw [ht, map_mul, map_mul]
    exact mul_le_of_le_one_right' (valued_ψ_le_one v t)
  · intro w' hw'
    obtain ⟨a, ha⟩ := exists_padicInt_of_valued_le_one v hw'.le
    obtain ⟨b, hb⟩ := exists_padicInt_of_valued_le_one v
      (show Valued.v ((w'⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 by
        rw [Units.val_inv_eq_inv_val, map_inv₀, hw', inv_one])
    have hab : a * b = 1 := (χ_injective v) (by
      rw [map_mul, map_one]; change ψ v a * ψ v b = 1; rw [ha, hb]; simp)
    obtain ⟨η, hη⟩ := hval a ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩
    refine ⟨fun i => χ v ((C *ᵥ η) i), ?_, ?_⟩
    · rw [hL]; exact (mem_tLat_iff v hC _).mpr ⟨η, rfl⟩
    · rw [evalIn_χ, hη, map_mul]; congr 1

end Transport

end QuadFormsKB.Cassels.Ch11L92
