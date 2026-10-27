/-
# Hanke, AWS 2009 notes, §4.2 and §4.5: adelic orthogonal groups and lattices

Concrete definitions for J. Hanke, *Quadratic Forms and Automorphic Forms* (bibkey `hanke2011aws`),
§4.2 (adelizations) and §4.5 (classes in a genus as double cosets). The list D1, D2, … of the
notes' derivations is in `AWS/Overview.lean`; this file is **D15** and **D16**.

Throughout, $H \in M_n(\mathbb{Q})$ is a symmetric matrix (in applications the Hessian
$C + C^{\mathsf T}$ of an integral form $Q$, `QuadForm.hessian`), $V = \mathbb{Q}^n$ with the form
$\tfrac12 x^{\mathsf T} H x$, and the reference lattice is $L = \mathbb{Z}^n$.

## Definitions (Mathlib where possible)

- `orthGroup H R` $= O(V)(R) = \{g \in \mathrm{GL}_n(R) : g^{\mathsf T} H g = H\}$ for any
  $\mathbb{Q}$-algebra $R$ ($\mathbb{Q}$, $\mathbb{Q}_p$, $\mathbb{R}$); Mathlib's `Matrix.GeneralLinearGroup`.
- `intStab H p` $= O(V)(\mathbb{Z}_p)$, the stabilizer of $\mathbb{Z}_p^n$ (entries of $g$ and $g^{-1}$ in
  $\mathbb{Z}_p$).
- `OAf H` $= O(V_{\mathbb{A}_f})$: the **restricted product** of the $O(V)(\mathbb{Q}_p)$ with respect to
  the $O(V)(\mathbb{Z}_p)$ (Mathlib's `RestrictedProduct`), exactly the notes' definition of the
  adelization on p. 56 ("$g_v \in G(\mathcal{O}_v)$ for all but finitely many $v$").
- `OA H` $= O(V_\mathbb{A}) = O(V)(\mathbb{R}) \times O(V_{\mathbb{A}_f})$, with the diagonal embedding
  `diag : O(V)(ℚ) →* OA H` and the adelic stabilizer `KA H` $= O(V)(\mathbb{R}) \times \prod_p O(V)(\mathbb{Z}_p)$.
- Lattices: `Lat n` (sets $g\mathbb{Z}^n \subset \mathbb{Q}^n$, $g \in \mathrm{GL}_n(\mathbb{Q})$), local lattices
  `LocLat p n` (sets $g\mathbb{Z}_p^n \subset \mathbb{Q}_p^n$), the localization `loc p L` $= L_p$.

## The input (Lemma 4.5.1)

`LatticeGluing n`: every family of local lattices, almost all equal to $\mathbb{Z}_p^n$, is the family
of localizations of a global lattice. This is the existence half of Lemma 4.5.1 (Shimura,
*Arithmetic of quadratic forms* (2010), Lem. 21.6; Weil, *Basic number theory*, Thm. 2, p. 84), which
the notes cite without proof. The other half is **proved** here: $L$ is determined by its
localizations (`mem_iff_forall_loc`: $L = \bigcap_p (V \cap L_p)$), and $L_p = \mathbb{Z}_p^n$ for almost
all $p$ (`loc_eventually_std`).

## Main results

- `latAction` (p. 61–62): the action of $O(V_\mathbb{A})$ on lattices, $h_\mathbb{A} L := $ the lattice
  with localizations $(h_p L_p)_p$; it ignores $h_\infty$.
- `diag_smul`: a rational $\gamma \in O(V)$ acts by $L \mapsto \gamma L$.
- `orbit_eq_genus` (**Lemma 4.5.2**, p. 62): the $O(V_\mathbb{A})$-orbit of $L$ is the genus of $L$.
- `stabilizer_std` (p. 62): $\mathrm{Stab}_\mathbb{A}(\mathbb{Z}^n) = K_\mathbb{A}$.
- `dosetEquivClassesInGenus` (**D16**, p. 62): $O(V)\backslash O(V_\mathbb{A})/K_\mathbb{A} \simeq$ classes in
  $\mathrm{Gen}(\mathbb{Z}^n)$.
- `card_aut_eq` ((4.11), p. 64): $|O(V) \cap \alpha K_\mathbb{A}\alpha^{-1}| = |\mathrm{Aut}(\alpha L)|$.

*Erratum (candidate; pending author):* p. 62, "Notice that this action makes no use of the
non-archimedian component $h_\infty$ of $h_\mathbb{A}$" should read "archimedean".

Following Tau Ceti (`TauCeti/NumberTheory/QuadraticForm/OrthogonalGroup/FiniteAdelic.lean`), the
finite adelic orthogonal group is a restricted product over `PrimeIdx`; we do not import Tau Ceti
and use matrices instead of its `QuadraticForm` isometries.
-/
import QuadFormsKB.Literature.AWS.DoubleCosets

open Matrix
open scoped RestrictedProduct Pointwise

namespace QuadFormsKB.AWS

/-- The index set of the finite places of $\mathbb{Q}$: the primes $p$, as a subtype of `ℕ` (the same
type as Mathlib's `Nat.Primes`, but reducible, so that `(p : ℕ)` is syntactically `Subtype.val p`). -/
abbrev PrimeIdx : Type := {p : ℕ // p.Prime}

/-- `Fact` that a bundled prime is prime, so that `ℚ_[p]` makes sense for `p : PrimeIdx`. -/
instance factPrimes (p : PrimeIdx) : Fact (p : ℕ).Prime := ⟨p.2⟩

variable {n : ℕ}

/-! ### The orthogonal group over a ℚ-algebra -/

/-- **The orthogonal group** $O(V)(R) = \{g \in \mathrm{GL}_n(R) : g^{\mathsf T} H g = H\}$ of the
symmetric matrix $H \in M_n(\mathbb{Q})$, over a $\mathbb{Q}$-algebra $R$ (notes, §4.2, p. 56, with
$G = O(Q)$; the task's definition $G(R) = \{g : g^{\mathsf T} A g = A\}$). For $H$ the Hessian of
$Q$ this is the group of $g$ with $Q(gx) = Q(x)$ (`orthGroup_eval`). -/
@[kb "hanke2011aws" "§4.2, p. 56"]
def orthGroup (H : Matrix (Fin n) (Fin n) ℚ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    Subgroup (GL (Fin n) R) where
  carrier := {g | g.valᵀ * H.map (algebraMap ℚ R) * g.val = H.map (algebraMap ℚ R)}
  mul_mem' {a b} ha hb := by
    change a.valᵀ * _ * a.val = _ at ha
    change b.valᵀ * _ * b.val = _ at hb
    change (a * b).valᵀ * _ * (a * b).val = _
    rw [Units.val_mul, transpose_mul]
    calc b.valᵀ * a.valᵀ * H.map (algebraMap ℚ R) * (a.val * b.val)
        = b.valᵀ * (a.valᵀ * H.map (algebraMap ℚ R) * a.val) * b.val := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]
  one_mem' := by change (1 : GL (Fin n) R).valᵀ * _ * (1 : GL (Fin n) R).val = _; simp
  inv_mem' {a} ha := by
    change a.valᵀ * _ * a.val = _ at ha
    change a⁻¹.valᵀ * _ * a⁻¹.val = _
    calc a⁻¹.valᵀ * H.map (algebraMap ℚ R) * a⁻¹.val
        = a⁻¹.valᵀ * (a.valᵀ * H.map (algebraMap ℚ R) * a.val) * a⁻¹.val := by rw [ha]
      _ = (a.val * a⁻¹.val)ᵀ * H.map (algebraMap ℚ R) * (a.val * a⁻¹.val) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.mul_inv]; simp

theorem mem_orthGroup {H : Matrix (Fin n) (Fin n) ℚ} {R : Type*} [CommRing R] [Algebra ℚ R]
    {g : GL (Fin n) R} :
    g ∈ orthGroup H R ↔ g.valᵀ * H.map (algebraMap ℚ R) * g.val = H.map (algebraMap ℚ R) :=
  Iff.rfl

/-- **Base change of rational isometries** $O(V)(\mathbb{Q}) \to O(V)(R)$, $\gamma \mapsto \gamma$ viewed
over $R$ (entrywise `algebraMap ℚ R`). -/
noncomputable def orthMap (H : Matrix (Fin n) (Fin n) ℚ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    orthGroup H ℚ →* orthGroup H R where
  toFun γ := ⟨GeneralLinearGroup.map (algebraMap ℚ R) (γ : GL (Fin n) ℚ), by
    have hγ := mem_orthGroup.mp γ.2
    rw [mem_orthGroup]
    have : ((GeneralLinearGroup.map (algebraMap ℚ R) (γ : GL (Fin n) ℚ)).val) =
        (γ : GL (Fin n) ℚ).val.map (algebraMap ℚ R) := rfl
    rw [this, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (·.map (algebraMap ℚ R)) hγ⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp

@[simp] theorem orthMap_val (H : Matrix (Fin n) (Fin n) ℚ) (R : Type*) [CommRing R] [Algebra ℚ R]
    (γ : orthGroup H ℚ) :
    ((orthMap H R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      (γ : GL (Fin n) ℚ).val.map (algebraMap ℚ R) := rfl

/-! ### p-adic integrality -/

section padic

variable (p : ℕ) [Fact p.Prime]

/-- **$p$-integral matrix:** every entry of $M \in M_n(\mathbb{Q}_p)$ lies in $\mathbb{Z}_p$
($\|M_{ij}\|_p \le 1$). -/
def IsIntP (M : Matrix (Fin n) (Fin n) ℚ_[p]) : Prop := ∀ i j, ‖M i j‖ ≤ 1

/-- **$p$-integral vector:** $w \in \mathbb{Z}_p^n$, i.e. $\|w_i\|_p \le 1$ for all $i$. -/
def IsIntVecP (w : Fin n → ℚ_[p]) : Prop := ∀ i, ‖w i‖ ≤ 1

variable {p}

theorem norm_sum_mul_le_one {ι : Type*} (s : Finset ι) (a b : ι → ℚ_[p]) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hb : ∀ i, ‖b i‖ ≤ 1) : ‖∑ i ∈ s, a i * b i‖ ≤ 1 := by
  have : (∑ i ∈ s, a i * b i) ∈ PadicInt.subring p :=
    Subring.sum_mem _ fun i _ => Subring.mul_mem _ (by simpa [PadicInt.mem_subring_iff] using ha i)
      (by simpa [PadicInt.mem_subring_iff] using hb i)
  simpa [PadicInt.mem_subring_iff] using this

theorem IsIntP.mul {M N : Matrix (Fin n) (Fin n) ℚ_[p]} (hM : IsIntP p M) (hN : IsIntP p N) :
    IsIntP p (M * N) := fun i j => by
  rw [Matrix.mul_apply]; exact norm_sum_mul_le_one _ _ _ (hM i) (fun k => hN k j)

theorem IsIntP.mulVec {M : Matrix (Fin n) (Fin n) ℚ_[p]} {w : Fin n → ℚ_[p]} (hM : IsIntP p M)
    (hw : IsIntVecP p w) : IsIntVecP p (M *ᵥ w) := fun i => by
  rw [Matrix.mulVec, dotProduct]; exact norm_sum_mul_le_one _ _ _ (hM i) hw

theorem IsIntP.one : IsIntP p (1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  intro i j; rw [Matrix.one_apply]; split_ifs <;> simp

/-- **The local stabilizer** $O(V)(\mathbb{Z}_p) = \{g \in O(V)(\mathbb{Q}_p) : g, g^{-1} \in M_n(\mathbb{Z}_p)\}$,
the stabilizer of $\mathbb{Z}_p^n$ (`locAct_std_iff`); the notes' $K_p = G(\mathcal{O}_p)$ (p. 56). -/
@[kb "hanke2011aws" "§4.2, p. 56"]
def intStab (H : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact p.Prime] : Subgroup (orthGroup H ℚ_[p]) where
  carrier := {g | IsIntP p (g : GL (Fin n) ℚ_[p]).val ∧ IsIntP p (g : GL (Fin n) ℚ_[p])⁻¹.val}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · change IsIntP p ((a : GL (Fin n) ℚ_[p]) * b).val
      rw [Units.val_mul]; exact ha.1.mul hb.1
    · change IsIntP p ((a : GL (Fin n) ℚ_[p]) * b)⁻¹.val
      rw [_root_.mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2
  one_mem' := ⟨by simpa using IsIntP.one, by simpa using IsIntP.one⟩
  inv_mem' {a} ha := ⟨by simpa using ha.2, by simpa using ha.1⟩

/-- For an integer $z$: $\|z\|_p < 1 \iff p \mid z$. -/
theorem norm_intCast_lt_one_iff (z : ℤ) : ‖(z : ℚ_[p])‖ < 1 ↔ (p : ℤ) ∣ z := by
  rw [← PadicInt.norm_int_lt_one_iff_dvd, PadicInt.norm_def]
  simp

/-- **A rational number is an integer iff it is $p$-integral at every prime $p$.** -/
theorem rat_isInt_iff (q : ℚ) :
    (∃ z : ℤ, q = z) ↔ ∀ p : PrimeIdx, ‖(q : ℚ_[(p : ℕ)])‖ ≤ 1 := by
  constructor
  · rintro ⟨z, rfl⟩ p
    simpa using Padic.norm_int_le_one (p := (p : ℕ)) z
  · intro h
    by_contra hq
    have hden : q.den ≠ 1 := fun h1 => hq ⟨q.num, (Rat.coe_int_num_of_den_eq_one h1).symm⟩
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hden
    haveI : Fact r.Prime := ⟨hr⟩
    have hq' := h ⟨r, hr⟩
    simp only at hq'
    -- ‖num‖ = ‖q‖ ‖den‖ < 1, so r ∣ num, contradicting coprimality
    have hdenlt : ‖((q.den : ℤ) : ℚ_[r])‖ < 1 := by
      rw [norm_intCast_lt_one_iff]; exact_mod_cast hrd
    have hnum : ‖((q.num : ℤ) : ℚ_[r])‖ < 1 := by
      have e : ((q.num : ℤ) : ℚ_[r]) = (q : ℚ_[r]) * ((q.den : ℤ) : ℚ_[r]) := by
        have : (q.num : ℚ) = q * (q.den : ℤ) := by
          push_cast; rw [Rat.mul_den_eq_num]
        exact_mod_cast congrArg (fun x : ℚ => (x : ℚ_[r])) this
      rw [e, norm_mul]
      calc ‖(q : ℚ_[r])‖ * ‖((q.den : ℤ) : ℚ_[r])‖ ≤ 1 * ‖((q.den : ℤ) : ℚ_[r])‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hdenlt
    rw [norm_intCast_lt_one_iff] at hnum
    have hcop := q.reduced
    have : r ∣ Nat.gcd q.num.natAbs q.den :=
      Nat.dvd_gcd (Int.natCast_dvd.mp hnum) hrd
    rw [hcop] at this
    exact hr.one_lt.ne' (Nat.dvd_one.mp this)

end padic

/-! ### The finite adelic and adelic orthogonal groups -/

/-- **The finite adelic orthogonal group** $O(V_{\mathbb{A}_f})$ (notes, §4.2, p. 56): the restricted
product $\prod'_p O(V)(\mathbb{Q}_p)$ with respect to the subgroups $O(V)(\mathbb{Z}_p)$ = `intStab H p`. -/
@[kb "hanke2011aws" "§4.2, p. 56"]
abbrev OAf (H : Matrix (Fin n) (Fin n) ℚ) : Type :=
  Πʳ p : PrimeIdx, [orthGroup H ℚ_[(p : ℕ)], intStab H (p : ℕ)]

/-- **The adelic orthogonal group** $O(V_\mathbb{A}) = O(V)(\mathbb{R}) \times O(V_{\mathbb{A}_f})$
(the archimedean factor is the whole group $O(V_\infty)$; for positive definite $H$ it is compact, so
$G(\mathcal{O}_\infty) = G(F_\infty)$ in the notes' convention). -/
@[kb "hanke2011aws" "§4.2, p. 56"]
abbrev OA (H : Matrix (Fin n) (Fin n) ℚ) : Type := orthGroup H ℝ × OAf H

/-- **The adelic stabilizer** $K_\mathbb{A} = O(V)(\mathbb{R}) \times \prod_p O(V)(\mathbb{Z}_p)$ of the
standard lattice (p. 62, $K_\mathbb{A} := \mathrm{Stab}_\mathbb{A}(L)$; see `stabilizer_std`). -/
@[kb "hanke2011aws" "§4.5, p. 62"]
def KA (H : Matrix (Fin n) (Fin n) ℚ) : Subgroup (OA H) where
  carrier := {h | ∀ p : PrimeIdx, h.2 p ∈ intStab H (p : ℕ)}
  mul_mem' ha hb p := (intStab H p).mul_mem (ha p) (hb p)
  one_mem' p := (intStab H p).one_mem
  inv_mem' ha p := (intStab H p).inv_mem (ha p)

/-! ### p-adic integrality of rational matrices -/

/-- The primes dividing a denominator of some entry of the rational matrix $M$. -/
def denPrimes (M : Matrix (Fin n) (Fin n) ℚ) : Finset ℕ :=
  Finset.univ.biUnion fun ij : Fin n × Fin n => (M ij.1 ij.2).den.primeFactors

/-- A rational matrix is $p$-integral at every prime $p$ outside `denPrimes`. -/
theorem isIntP_map_of_not_mem (M : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [hp : Fact p.Prime]
    (h : p ∉ denPrimes M) : IsIntP p (M.map (algebraMap ℚ ℚ_[p])) := by
  intro i j
  simp only [Matrix.map_apply, eq_ratCast]
  apply Padic.norm_rat_le_one
  intro hd
  apply h
  simp only [denPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and, Nat.mem_primeFactors]
  exact ⟨(i, j), hp.out, hd, (M i j).den_nz⟩

/-- A finite set of naturals contains only finitely many bundled primes. -/
theorem finite_primes_mem (S : Finset ℕ) : {p : PrimeIdx | (p : ℕ) ∈ S}.Finite :=
  (S.finite_toSet).preimage (fun _ _ _ _ h => Subtype.ext h)

/-- **A rational $\gamma \in \mathrm{GL}_n(\mathbb{Q})$ lies in $\mathrm{GL}_n(\mathbb{Z}_p)$ for almost
all $p$.** -/
theorem eventually_isIntP (g : GL (Fin n) ℚ) :
    ∀ᶠ p : PrimeIdx in Filter.cofinite,
      IsIntP (p : ℕ) (g.val.map (algebraMap ℚ ℚ_[(p : ℕ)])) ∧
        IsIntP (p : ℕ) (g⁻¹.val.map (algebraMap ℚ ℚ_[(p : ℕ)])) := by
  rw [Filter.eventually_cofinite]
  refine (finite_primes_mem (denPrimes g.val ∪ denPrimes g⁻¹.val)).subset ?_
  intro p hp
  by_contra hmem
  rw [Set.mem_ofPred_eq, Finset.mem_union, not_or] at hmem
  exact hp ⟨isIntP_map_of_not_mem _ (p : ℕ) hmem.1, isIntP_map_of_not_mem _ (p : ℕ) hmem.2⟩

/-- **The diagonal embedding** $O(V)(\mathbb{Q}) \to O(V_{\mathbb{A}_f})$, $\gamma \mapsto (\gamma)_p$ (p. 56:
the restricted product "is large enough to contain all rational points $G(F)$"). -/
noncomputable def diagF (H : Matrix (Fin n) (Fin n) ℚ) : orthGroup H ℚ →* OAf H where
  toFun γ := ⟨fun p => orthMap H ℚ_[(p : ℕ)] γ, by
    filter_upwards [eventually_isIntP (γ : GL (Fin n) ℚ)] with p hp
    refine ⟨by simpa using hp.1, ?_⟩
    have : ((orthMap H ℚ_[(p : ℕ)] γ : GL (Fin n) ℚ_[(p : ℕ)])⁻¹).val =
        (γ : GL (Fin n) ℚ)⁻¹.val.map (algebraMap ℚ ℚ_[(p : ℕ)]) := by
      show ((GeneralLinearGroup.map (algebraMap ℚ ℚ_[(p : ℕ)]) (γ : GL (Fin n) ℚ))⁻¹).val = _
      rw [← GeneralLinearGroup.map_inv]; rfl
    rw [this]; exact hp.2⟩
  map_one' := by ext p : 1; exact map_one (orthMap H ℚ_[(p : ℕ)])
  map_mul' a b := by ext p : 1; exact map_mul (orthMap H ℚ_[(p : ℕ)]) a b

/-- **The diagonal embedding** $\gamma \mapsto (\gamma_\infty, (\gamma_p)_p)$ of $O(V)$ into
$O(V_\mathbb{A})$ ("the canonical diagonal embedding $\gamma \mapsto (\gamma, \gamma, \dots)$", p. 57). -/
noncomputable def diag (H : Matrix (Fin n) (Fin n) ℚ) : orthGroup H ℚ →* OA H :=
  (orthMap H ℝ).prod (diagF H)

/-- **The rational points** $O(V) \le O(V_\mathbb{A})$, embedded diagonally. -/
noncomputable abbrev ratPoints (H : Matrix (Fin n) (Fin n) ℚ) : Subgroup (OA H) := (diag H).range

theorem diag_injective (H : Matrix (Fin n) (Fin n) ℚ) : Function.Injective (diag H) := by
  intro a b h
  have h1 := congrArg (fun x => ((x.1 : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) h
  simp only [diag, MonoidHom.prod_apply, orthMap_val] at h1
  apply Subtype.ext; apply Units.ext
  ext i j
  have := congrFun (congrFun h1 i) j
  simpa using this

/-! ### Lattices -/

/-- **Integral rational vector:** $v \in \mathbb{Z}^n$. -/
def IsIntVec (v : Fin n → ℚ) : Prop := ∀ i, ∃ z : ℤ, v i = z

/-- The lattice $g\mathbb{Z}^n = \{v \in \mathbb{Q}^n : g^{-1}v \in \mathbb{Z}^n\}$ spanned by the columns of
$g \in \mathrm{GL}_n(\mathbb{Q})$. -/
def latOf (g : GL (Fin n) ℚ) : Set (Fin n → ℚ) := {v | IsIntVec (g⁻¹.val *ᵥ v)}

/-- **Lattices in $V = \mathbb{Q}^n$** (full $\mathbb{Z}$-lattices): the sets $g\mathbb{Z}^n$,
$g \in \mathrm{GL}_n(\mathbb{Q})$. -/
abbrev Lat (n : ℕ) : Type := {L : Set (Fin n → ℚ) // ∃ g : GL (Fin n) ℚ, L = latOf g}

/-- The local lattice $g\mathbb{Z}_p^n = \{w \in \mathbb{Q}_p^n : g^{-1}w \in \mathbb{Z}_p^n\}$. -/
def latOfP (p : ℕ) [Fact p.Prime] (g : GL (Fin n) ℚ_[p]) : Set (Fin n → ℚ_[p]) :=
  {w | IsIntVecP p (g⁻¹.val *ᵥ w)}

/-- **Local lattices in $V_p = \mathbb{Q}_p^n$:** the sets $g\mathbb{Z}_p^n$, $g \in \mathrm{GL}_n(\mathbb{Q}_p)$
(the full $\mathbb{Z}_p$-lattices). -/
abbrev LocLat (p : ℕ) [Fact p.Prime] (n : ℕ) : Type :=
  {M : Set (Fin n → ℚ_[p]) // ∃ g : GL (Fin n) ℚ_[p], M = latOfP p g}

/-- The standard local lattice $\mathbb{Z}_p^n$. -/
def stdLoc (p : ℕ) [Fact p.Prime] : LocLat p n := ⟨latOfP p 1, 1, rfl⟩

/-- The standard lattice $L = \mathbb{Z}^n$. -/
def stdLat : Lat n := ⟨latOf 1, 1, rfl⟩

theorem Lat.ext {L L' : Lat n} (h : L.1 = L'.1) : L = L' := Subtype.ext h
theorem LocLat.ext {p : ℕ} [Fact p.Prime] {M M' : LocLat p n} (h : M.1 = M'.1) : M = M' :=
  Subtype.ext h

section loc

variable (p : ℕ) [Fact p.Prime]

/-- Base change of a rational invertible matrix to $\mathbb{Q}_p$. -/
noncomputable abbrev glP (g : GL (Fin n) ℚ) : GL (Fin n) ℚ_[p] :=
  GeneralLinearGroup.map (algebraMap ℚ ℚ_[p]) g

theorem glP_inv_val (g : GL (Fin n) ℚ) :
    ((glP p g)⁻¹).val = g⁻¹.val.map (algebraMap ℚ ℚ_[p]) := by
  rw [← map_inv]; rfl

theorem mulVec_cast (M : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    M.map (algebraMap ℚ ℚ_[p]) *ᵥ (fun i => (v i : ℚ_[p])) = fun i => (((M *ᵥ v) i : ℚ) : ℚ_[p]) := by
  funext i
  have := (RingHom.map_mulVec (algebraMap ℚ ℚ_[p]) M v i).symm
  simpa [Function.comp_def] using this

/-- If $g\mathbb{Z}^n = g'\mathbb{Z}^n$ then $g'^{-1}g$ has integer entries. -/
theorem isInt_of_latOf_eq {g g' : GL (Fin n) ℚ} (h : latOf g = latOf g') (i j : Fin n) :
    ∃ z : ℤ, (g'⁻¹.val * g.val) i j = z := by
  have hmem : g.val *ᵥ Pi.single j 1 ∈ latOf g := by
    show IsIntVec (g⁻¹.val *ᵥ (g.val *ᵥ Pi.single j 1))
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    intro k
    by_cases hk : k = j
    · exact ⟨1, by subst hk; simp⟩
    · exact ⟨0, by simp [hk]⟩
  rw [h] at hmem
  obtain ⟨z, hz⟩ := hmem i
  refine ⟨z, ?_⟩
  rw [mulVec_mulVec, mulVec_single, Pi.smul_apply] at hz
  simpa using hz

theorem isIntP_map_of_isInt (M : Matrix (Fin n) (Fin n) ℚ) (hM : ∀ i j, ∃ z : ℤ, M i j = z) :
    IsIntP p (M.map (algebraMap ℚ ℚ_[p])) := by
  intro i j
  obtain ⟨z, hz⟩ := hM i j
  simp only [Matrix.map_apply, hz, eq_ratCast, Rat.cast_intCast]
  exact Padic.norm_int_le_one z

/-- **Localization is well defined:** if $g\mathbb{Z}^n = g'\mathbb{Z}^n$ then $g\mathbb{Z}_p^n = g'\mathbb{Z}_p^n$. -/
theorem latOfP_eq_of_latOf_eq {g g' : GL (Fin n) ℚ} (h : latOf g = latOf g') :
    latOfP p (glP p g) = latOfP p (glP p g') := by
  have key : ∀ {g g' : GL (Fin n) ℚ}, latOf g = latOf g' →
      latOfP p (glP p g) ⊆ latOfP p (glP p g') := by
    intro g g' h w hw
    show IsIntVecP p ((glP p g')⁻¹.val *ᵥ w)
    have e : (glP p g')⁻¹.val *ᵥ w =
        (g'⁻¹.val * g.val).map (algebraMap ℚ ℚ_[p]) *ᵥ ((glP p g)⁻¹.val *ᵥ w) := by
      rw [mulVec_mulVec, Matrix.map_mul, glP_inv_val, glP_inv_val, Matrix.mul_assoc,
        ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (by simp)
        (by simp), Matrix.mul_one]
    rw [e]
    exact (isIntP_map_of_isInt p _ (isInt_of_latOf_eq h)).mulVec hw
  exact (key h).antisymm (key h.symm)

/-- **The localization** $L_p = L \otimes \mathbb{Z}_p$ of a lattice $L = g\mathbb{Z}^n$: the local lattice
$g\mathbb{Z}_p^n$ (independent of $g$ by `latOfP_eq_of_latOf_eq`; Lemma 4.5.1's map
$L \mapsto (L_p)_p$, p. 61). -/
noncomputable def loc (L : Lat n) : LocLat p n :=
  ⟨latOfP p (glP p L.2.choose), glP p L.2.choose, rfl⟩

theorem loc_eq_of (L : Lat n) {g : GL (Fin n) ℚ} (hg : L.1 = latOf g) :
    (loc p L).1 = latOfP p (glP p g) :=
  latOfP_eq_of_latOf_eq p (L.2.choose_spec.symm.trans hg)

end loc

/-- **$L = \bigcap_p (V \cap L_p)$** (Lemma 4.5.1, the inverse map, p. 61): $v \in L$ iff
$v \in L_p$ for every prime $p$. Proved (it is the injectivity half of Lemma 4.5.1). -/
@[kb "hanke2011aws" "§4.5, Lemma 4.5.1, p. 61"]
theorem mem_iff_forall_loc (L : Lat n) (v : Fin n → ℚ) :
    v ∈ L.1 ↔ ∀ p : PrimeIdx, (fun i => (v i : ℚ_[(p : ℕ)])) ∈ (loc (p : ℕ) L).1 := by
  obtain ⟨g, hg⟩ := L.2
  simp only [loc_eq_of _ L hg, hg, latOf, latOfP, Set.mem_ofPred_eq, IsIntVec, IsIntVecP]
  constructor
  · intro h p i
    rw [glP_inv_val, mulVec_cast]
    obtain ⟨z, hz⟩ := h i
    beta_reduce
    rw [hz]; simpa using Padic.norm_int_le_one (p := (p : ℕ)) z
  · intro h i
    rw [rat_isInt_iff]
    intro p
    have := h p i
    rw [glP_inv_val, mulVec_cast] at this
    exact this

/-- **Lattices are determined by their localizations** (Lemma 4.5.1, injectivity). -/
theorem loc_injective {L L' : Lat n} (h : ∀ p : PrimeIdx, loc (p : ℕ) L = loc (p : ℕ) L') :
    L = L' := by
  apply Lat.ext; ext v
  rw [mem_iff_forall_loc, mem_iff_forall_loc]
  simp only [h]

/-- If $g, g^{-1}$ are $p$-integral then $g\mathbb{Z}_p^n = \mathbb{Z}_p^n$. -/
theorem latOfP_eq_std {p : ℕ} [Fact p.Prime] {g : GL (Fin n) ℚ_[p]} (h1 : IsIntP p g.val)
    (h2 : IsIntP p g⁻¹.val) : latOfP p g = latOfP p 1 := by
  ext w
  simp only [latOfP, Set.mem_ofPred_eq, inv_one, Units.val_one, one_mulVec]
  constructor
  · intro hw
    have : w = g.val *ᵥ (g⁻¹.val *ᵥ w) := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [this]; exact h1.mulVec hw
  · intro hw; exact h2.mulVec hw

/-- **$L_p = \mathbb{Z}_p^n$ for almost all $p$** (Lemma 4.5.1: "all but finitely many $L_p$ are equal
to $\mathcal{O}_p^n$"). Proved. -/
@[kb "hanke2011aws" "§4.5, Lemma 4.5.1, p. 61"]
theorem loc_eventually_std (L : Lat n) :
    ∀ᶠ p : PrimeIdx in Filter.cofinite, loc (p : ℕ) L = stdLoc (p : ℕ) := by
  obtain ⟨g, hg⟩ := L.2
  filter_upwards [eventually_isIntP g] with p hp
  apply LocLat.ext
  rw [loc_eq_of _ L hg]
  exact latOfP_eq_std hp.1 (by rw [glP_inv_val]; exact hp.2)

/-! ### The local action and the gluing input -/

/-- **The action of $\mathrm{GL}_n(\mathbb{Q}_p)$ on local lattices:** $g \cdot M = gM$ (image). -/
def locAct {p : ℕ} [Fact p.Prime] (g : GL (Fin n) ℚ_[p]) (M : LocLat p n) : LocLat p n :=
  ⟨(g.val *ᵥ ·) '' M.1, by
    obtain ⟨m, hm⟩ := M.2
    refine ⟨g * m, ?_⟩
    rw [hm]
    ext w
    simp only [latOfP, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
      exact hu
    · intro hw
      refine ⟨g⁻¹.val *ᵥ w, ?_, ?_⟩
      · rw [mulVec_mulVec, ← Units.val_mul, ← _root_.mul_inv_rev]; exact hw
      · rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩

theorem locAct_one {p : ℕ} [Fact p.Prime] (M : LocLat p n) : locAct 1 M = M := by
  apply LocLat.ext; simp [locAct]

theorem locAct_mul {p : ℕ} [Fact p.Prime] (g h : GL (Fin n) ℚ_[p]) (M : LocLat p n) :
    locAct (g * h) M = locAct g (locAct h M) := by
  apply LocLat.ext
  simp only [locAct, Units.val_mul, ← Set.image_comp]
  congr 1; funext w; simp [mulVec_mulVec]

theorem locAct_latOfP {p : ℕ} [Fact p.Prime] (g m : GL (Fin n) ℚ_[p]) :
    (locAct g ⟨latOfP p m, m, rfl⟩).1 = latOfP p (g * m) := by
  ext w
  simp only [locAct, latOfP, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]; exact hu
  · intro hw
    refine ⟨g⁻¹.val *ᵥ w, ?_, ?_⟩
    · rw [mulVec_mulVec, ← Units.val_mul, ← _root_.mul_inv_rev]; exact hw
    · rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

/-- **$g\mathbb{Z}_p^n = \mathbb{Z}_p^n$ iff $g \in \mathrm{GL}_n(\mathbb{Z}_p)$.** -/
theorem locAct_std_iff {p : ℕ} [Fact p.Prime] (g : GL (Fin n) ℚ_[p]) :
    locAct g (stdLoc p) = stdLoc p ↔ IsIntP p g.val ∧ IsIntP p g⁻¹.val := by
  constructor
  · intro h
    have h' : latOfP p g = latOfP p 1 := by
      have := congrArg Subtype.val h
      rwa [stdLoc, locAct_latOfP, mul_one] at this
    have e : ∀ j : Fin n, (Pi.single j 1 : Fin n → ℚ_[p]) ∈ latOfP p 1 := by
      intro j i
      simp only [inv_one, Units.val_one, one_mulVec, Pi.single_apply]
      split_ifs <;> simp
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · -- column j of g is g e_j ∈ g ℤ_p^n = ℤ_p^n
      have hm : g.val *ᵥ Pi.single j 1 ∈ latOfP p g := by
        show IsIntVecP p (g⁻¹.val *ᵥ (g.val *ᵥ Pi.single j 1))
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
        have := e j
        simpa [latOfP] using this
      rw [h'] at hm
      have := hm i
      simpa [latOfP, mulVec_single] using this
    · have hm := e j
      rw [← h'] at hm
      have := hm i
      simpa [mulVec_single] using this
  · rintro ⟨h1, h2⟩
    apply LocLat.ext
    rw [stdLoc, locAct_latOfP, mul_one]
    exact latOfP_eq_std h1 h2

/-- **Input (Lemma 4.5.1, existence half, p. 61).** Every family $(M_p)_p$ of local lattices
$M_p \subset \mathbb{Q}_p^n$ with $M_p = \mathbb{Z}_p^n$ for all but finitely many $p$ is the family of
localizations of a lattice $L \subset \mathbb{Q}^n$ (namely $L = \bigcap_p (\mathbb{Q}^n \cap M_p)$).
Cited in the notes from Shimura, *Arithmetic of Quadratic Forms* (2010), Lemma 21.6, pp. 102–103,
and Weil, *Basic Number Theory*, Ch. V, Thm. 2, p. 84. The uniqueness half is proved
(`loc_injective`). -/
def LatticeGluing (n : ℕ) : Prop :=
  ∀ M : (p : PrimeIdx) → LocLat (p : ℕ) n,
    (∀ᶠ p : PrimeIdx in Filter.cofinite, M p = stdLoc (p : ℕ)) →
      ∃ L : Lat n, ∀ p : PrimeIdx, loc (p : ℕ) L = M p

variable (H : Matrix (Fin n) (Fin n) ℚ)

/-- The local lattices $(h_p L_p)_p$ for $h \in O(V_\mathbb{A})$: almost all are standard. -/
theorem eventually_locAct_std (h : OA H) (L : Lat n) :
    ∀ᶠ p : PrimeIdx in Filter.cofinite,
      locAct ((h.2 p : orthGroup H ℚ_[(p : ℕ)]) : GL (Fin n) ℚ_[(p : ℕ)]) (loc (p : ℕ) L) =
        stdLoc (p : ℕ) := by
  filter_upwards [h.2.2, loc_eventually_std L] with p hp hL
  rw [hL]; exact (locAct_std_iff _).mpr hp

/-- **The action of $O(V_\mathbb{A})$ on lattices** (p. 61–62): $h_\mathbb{A} \cdot L$ is the lattice whose
localizations are $h_p L_p$ (it exists by the input `LatticeGluing` and is unique by
`loc_injective`). "This action makes no use of the [archimedean] component $h_\infty$." -/
@[kb "hanke2011aws" "§4.5, pp. 61-62"]
noncomputable def latSMul (hG : LatticeGluing n) (h : OA H) (L : Lat n) : Lat n :=
  (hG _ (eventually_locAct_std H h L)).choose

theorem loc_latSMul (hG : LatticeGluing n) (h : OA H) (L : Lat n) (p : PrimeIdx) :
    loc (p : ℕ) (latSMul H hG h L) =
      locAct ((h.2 p : orthGroup H ℚ_[(p : ℕ)]) : GL (Fin n) ℚ_[(p : ℕ)]) (loc (p : ℕ) L) :=
  (hG _ (eventually_locAct_std H h L)).choose_spec p

/-- **The action of $O(V_\mathbb{A})$ on lattices is a group action.** -/
@[instance_reducible]
noncomputable def latAction (hG : LatticeGluing n) : MulAction (OA H) (Lat n) where
  smul := latSMul H hG
  one_smul L := loc_injective fun p => by
    change loc _ (latSMul H hG 1 L) = _
    rw [loc_latSMul]; exact locAct_one _
  mul_smul a b L := loc_injective fun p => by
    change loc _ (latSMul H hG (a * b) L) = loc _ (latSMul H hG a (latSMul H hG b L))
    rw [loc_latSMul, loc_latSMul, loc_latSMul]
    exact locAct_mul _ _ _

/-- **The image $\gamma L$ of a lattice** under $\gamma \in \mathrm{GL}_n(\mathbb{Q})$. -/
def latImage (γ : GL (Fin n) ℚ) (L : Lat n) : Lat n :=
  ⟨(γ.val *ᵥ ·) '' L.1, by
    obtain ⟨g, hg⟩ := L.2
    refine ⟨γ * g, ?_⟩
    rw [hg]
    ext w
    simp only [latOf, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]; exact hu
    · intro hw
      refine ⟨γ⁻¹.val *ᵥ w, ?_, ?_⟩
      · rw [mulVec_mulVec, ← Units.val_mul, ← _root_.mul_inv_rev]; exact hw
      · rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩

theorem latImage_eq (γ g : GL (Fin n) ℚ) (L : Lat n) (hg : L.1 = latOf g) :
    (latImage γ L).1 = latOf (γ * g) := by
  ext w
  simp only [latImage, hg, latOf, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]; exact hu
  · intro hw
    refine ⟨γ⁻¹.val *ᵥ w, ?_, ?_⟩
    · rw [mulVec_mulVec, ← Units.val_mul, ← _root_.mul_inv_rev]; exact hw
    · rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

/-- **A rational isometry acts on lattices by $L \mapsto \gamma L$** (p. 62: "two lattices in $(V,Q)$
are in the same class if they are isometric, hence they differ by the action of an element of
$O(V)$"). -/
@[kb "hanke2011aws" "§4.5, p. 62"]
theorem diag_smul (hG : LatticeGluing n) (γ : orthGroup H ℚ) (L : Lat n) :
    latSMul H hG (diag H γ) L = latImage (γ : GL (Fin n) ℚ) L := by
  apply loc_injective; intro p
  rw [loc_latSMul]
  obtain ⟨g, hg⟩ := L.2
  have hl : loc (p : ℕ) L = ⟨latOfP (p : ℕ) (glP (p : ℕ) g), glP (p : ℕ) g, rfl⟩ :=
    LocLat.ext (loc_eq_of _ L hg)
  have : (((diag H γ).2 p : orthGroup H ℚ_[(p : ℕ)]) : GL (Fin n) ℚ_[(p : ℕ)]) =
      glP (p : ℕ) (γ : GL (Fin n) ℚ) := rfl
  apply LocLat.ext
  rw [loc_eq_of _ _ (latImage_eq _ g L hg), hl, locAct_latOfP, this,
    show glP (p : ℕ) ((γ : GL (Fin n) ℚ) * g) = glP (p : ℕ) (γ : GL (Fin n) ℚ) * glP (p : ℕ) g from
      map_mul _ _ _]

/-- **The genus of a lattice** $L \subset V$ (p. 62, proof of Lemma 4.5.2): the lattices $L'$ in $V$
that are locally isometric to $L$ at every prime, $L'_p = h_pL_p$ for some $h_p \in O(V_p)$.
(The archimedean condition is automatic: "Since $L' \subset (V,Q)$ we see they are also isometric at
the archimedean place $\infty$".) -/
@[kb "hanke2011aws" "§4.5, Lemma 4.5.2, p. 62"]
def latGenus (L : Lat n) : Set (Lat n) :=
  {L' | ∀ p : PrimeIdx, ∃ h : orthGroup H ℚ_[(p : ℕ)],
    locAct (h : GL (Fin n) ℚ_[(p : ℕ)]) (loc (p : ℕ) L) = loc (p : ℕ) L'}

/-- **Lemma 4.5.2 (p. 62): the orbit of $L$ under $O(V_\mathbb{A})$ is the genus of $L$**, relative to
the gluing input (Lemma 4.5.1). For the converse inclusion the notes take "$h_p$ to be the element of
the orthogonal group carrying $L_p$ to $L'_p$ at the finitely many primes where $L_p \ne L'_p$, and
… all other components $h_v$ as the identity". -/
@[kb "hanke2011aws" "§4.5, Lemma 4.5.2, p. 62"]
theorem orbit_eq_genus (hG : LatticeGluing n) (L : Lat n) :
    @MulAction.orbit (OA H) (Lat n) (latAction H hG).toSMul L = latGenus H L := by
  letI := latAction H hG
  ext L'
  constructor
  · rintro ⟨h, rfl⟩ p
    exact ⟨h.2 p, (loc_latSMul H hG h L p).symm⟩
  · intro hL'
    classical
    choose k hk using hL'
    -- use the identity where L_p = L'_p
    let hp : (p : PrimeIdx) → orthGroup H ℚ_[(p : ℕ)] := fun p =>
      if loc (p : ℕ) L = loc (p : ℕ) L' then 1 else k p
    have hpspec : ∀ p : PrimeIdx, locAct ((hp p : orthGroup H ℚ_[(p : ℕ)]) : GL (Fin n) ℚ_[(p : ℕ)])
        (loc (p : ℕ) L) = loc (p : ℕ) L' := by
      intro p
      simp only [hp]
      split_ifs with he
      · rw [← he]; exact locAct_one _
      · exact hk p
    have hev : ∀ᶠ p : PrimeIdx in Filter.cofinite, hp p ∈ intStab H (p : ℕ) := by
      filter_upwards [loc_eventually_std L, loc_eventually_std L'] with p h1 h2
      simp [hp, h1, h2]
    let hA : OA H := (1, ⟨hp, hev⟩)
    refine ⟨hA, loc_injective fun p => ?_⟩
    change loc _ (latSMul H hG hA L) = _
    rw [loc_latSMul]
    exact hpspec p

/-- The localization of $\mathbb{Z}^n$ is $\mathbb{Z}_p^n$. -/
theorem loc_stdLat (p : ℕ) [Fact p.Prime] : loc p (stdLat (n := n)) = stdLoc p := by
  apply LocLat.ext
  rw [loc_eq_of _ stdLat rfl, stdLoc]
  congr 1; simp [glP]

/-- **Membership in $\alpha\mathbb{Z}^n$:** $\vec v \in \alpha_\mathbb{A}\mathbb{Z}^n$ iff
$\alpha_p^{-1}\vec v \in \mathbb{Z}_p^n$ for every prime $p$. -/
theorem mem_latSMul_std_iff (hG : LatticeGluing n) (α : OA H) (v : Fin n → ℚ) :
    v ∈ (latSMul H hG α stdLat).1 ↔ ∀ p : PrimeIdx,
      IsIntVecP (p : ℕ) ((((α.2 p) : orthGroup H ℚ_[(p : ℕ)]) : GL (Fin n) ℚ_[(p : ℕ)])⁻¹.val *ᵥ
        fun i => (v i : ℚ_[(p : ℕ)])) := by
  rw [mem_iff_forall_loc]
  refine forall_congr' fun p => ?_
  rw [loc_latSMul, loc_stdLat]
  change _ ∈ (locAct _ ⟨latOfP _ 1, 1, rfl⟩).1 ↔ _
  rw [locAct_latOfP, mul_one]
  rfl

/-- **$\mathrm{Stab}_\mathbb{A}(\mathbb{Z}^n) = K_\mathbb{A}$** (p. 62): $h_\mathbb{A}\mathbb{Z}^n = \mathbb{Z}^n$ iff
$h_p \in O(V)(\mathbb{Z}_p)$ for every $p$. -/
@[kb "hanke2011aws" "§4.5, p. 62"]
theorem stabilizer_std (hG : LatticeGluing n) :
    @MulAction.stabilizer (OA H) (Lat n) _ (latAction H hG) stdLat = KA H := by
  letI := latAction H hG
  ext h
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hh p
    have := congrArg (loc (p : ℕ)) hh
    change loc _ (latSMul H hG h stdLat) = _ at this
    rw [loc_latSMul] at this
    have hstd : loc (p : ℕ) (stdLat (n := n)) = stdLoc (p : ℕ) := loc_stdLat _
    rw [hstd] at this
    exact (locAct_std_iff _).mp this
  · intro hh
    apply loc_injective; intro p
    change loc _ (latSMul H hG h stdLat) = _
    rw [loc_latSMul]
    have hstd : loc (p : ℕ) (stdLat (n := n)) = stdLoc (p : ℕ) := loc_stdLat _
    rw [hstd]
    exact (locAct_std_iff _).mpr (hh p)

/-- **D16, concrete (p. 62): the class set as a double coset space.**
$$O(V)\backslash O(V_\mathbb{A})/K_\mathbb{A} \;\simeq\; \{\text{classes in } \mathrm{Gen}(\mathbb{Z}^n)\},$$
where a class is an $O(V)$-orbit of lattices $L' \subset V$ in the genus (`orbit_eq_genus`), and
$O(V)$ acts by $L' \mapsto \gamma L'$ (`diag_smul`). Relative to the input `LatticeGluing`
(Lemma 4.5.1). -/
@[kb "hanke2011aws" "§4.5, p. 62"]
noncomputable def dosetEquivClassesInGenus (hG : LatticeGluing n) :
    DoubleCoset.Quotient (ratPoints H : Set (OA H)) (KA H) ≃
      @ClassesInGenus (OA H) (Lat n) _ (latAction H hG) (ratPoints H) stdLat := by
  letI := latAction H hG
  rw [← stabilizer_std H hG]
  exact dosetEquivClasses (ratPoints H) stdLat

/-- **The automorphism group** $\mathrm{Aut}(L) = \{\gamma \in O(V) : \gamma L = L\}$ of a lattice
$L \subset V$ (§4.6, p. 64). -/
def autLat (L : Lat n) : Set (orthGroup H ℚ) := {γ | latImage (γ : GL (Fin n) ℚ) L = L}

/-- **(4.11), p. 64: $O(V) \cap K_{i,\mathbb{A}} = \mathrm{Aut}(L_i)$.** For $\alpha \in O(V_\mathbb{A})$ and
$L_\alpha := \alpha\mathbb{Z}^n$, the rational points of $\alpha K_\mathbb{A}\alpha^{-1}$ are in bijection
with $\mathrm{Aut}(L_\alpha)$ (via the diagonal embedding, which is injective). -/
@[kb "hanke2011aws" "§4.6, (4.11), p. 64"]
theorem card_aut_eq (hG : LatticeGluing n) (α : OA H) :
    Nat.card (ratPoints H ⊓ conjSub α (KA H) : Subgroup (OA H)) =
      Nat.card (autLat H (latSMul H hG α stdLat)) := by
  letI := latAction H hG
  rw [← stabilizer_std H hG, ← stabilizer_smul]
  symm
  refine Nat.card_congr
    { toFun := fun γ => ⟨diag H γ.1, ⟨⟨γ.1, rfl⟩, ?_⟩⟩
      invFun := fun h => ⟨h.2.1.choose, ?_⟩
      left_inv := fun γ => ?_
      right_inv := fun h => ?_ }
  · refine MulAction.mem_stabilizer_iff.mpr ?_
    change latSMul H hG (diag H γ.1) _ = _
    rw [diag_smul]; exact γ.2
  · show latImage _ _ = _
    rw [← diag_smul H hG, h.2.1.choose_spec]
    exact MulAction.mem_stabilizer_iff.mp h.2.2
  · apply Subtype.ext
    apply diag_injective H
    exact (⟨γ.1, rfl⟩ : diag H γ.1 ∈ (diag H).range).choose_spec
  · apply Subtype.ext
    exact h.2.1.choose_spec

end QuadFormsKB.AWS
