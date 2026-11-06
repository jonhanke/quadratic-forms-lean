/-
# Cassels, Chapter 8, Example 8: a recursive sequence of $\mathbb Z_p$-lattices

**Setting** (as in `Ch8/Maximal.lean`): $(V, \varphi)$ a quadratic space over $\mathbb Q_p$
(`Q : QuadraticForm ℚ_[p] V`), $\mathbb Z_p$-lattices are $\mathbb Z_p$-submodules of $V$ that are lattices on $V$
(`Submodule.IsLattice`), $O'Meara$'s $B$ (`OMeara.bil`) is Cassels' $\varphi(\vec x, \vec y)$. Congruences
$a \equiv b \pmod{p^{k}}$ between values of $\varphi$ are $|a - b| \le p^{-k}$ ($p$-adic norm).

**Defines**
* `ex8Op Q Λ` (Cassels' $\Gamma$): the set of $\vec d \in \Lambda$ with $\varphi(\vec c + \vec d) \equiv \varphi(\vec c)
  \pmod p$ for all $\vec c \in \Lambda$ (a $\mathbb Z_p$-submodule);
* `ex8Seq Q Λ m` (Cassels' $\Lambda_m$): $\Lambda_0 = \Lambda$, $\Lambda_{m+1} = p^{-1}\Delta_m$, where $\Delta_m$ is
  obtained from $\Gamma_m = $ `ex8Op Q Λ_m` as $\Gamma_m$ was from $\Lambda_m$ but with $p^{-1}\varphi$ instead of
  $\varphi$: $\Delta_m$ = `ex8Op (p⁻¹ • Q) Γ_m`. Here $p^{-1}\Delta = \{\vec x : p\vec x \in \Delta\}$.

**Proves** (Example 8, p. 126; $\varphi(\vec c) \in \mathbb Z_p$ for all $\vec c \in \Lambda$)
* `ex8_isLattice`, `ex8_norm`, `ex8_between` (**(i)**): (a) $\Gamma$ is a lattice, (b) $\varphi(\vec d) \in p\mathbb Z_p$
  for $\vec d \in \Gamma$, (c) $p\Lambda \subseteq \Gamma \subseteq \Lambda$;
* `ex8_ii` (**(ii)**): $\Delta \supseteq p\Lambda$ (the printed inclusion is garbled in the scan; it is reconstructed as
  the one needed in (iii));
* `ex8_seq_mono`, `ex8_seq_isLattice`, `ex8_seq_integral`, `ex8_seq_stabilizes` (**(iii)**):
  $\Lambda_m \subseteq \Lambda_{m+1}$, each $\Lambda_m$ is a lattice on which $\varphi$ is integer-valued, and for a
  regular space there is some $m$ with $\Lambda_{m+1} = \Lambda_m$;
* `ex8_iv` (**(iv)**): for $p \ne 2$ and a regular space, if $\Lambda_{m+1} = \Lambda_m$ then $\Lambda_m$ has a basis
  with $\varphi(\sum x_j\vec b_j) = \sum c_jx_j^{2}$ and $|c_j| \in \{1, p^{-1}\}$ for each $j$. (The scan reads
  "suppose that $p \ne 2$ and that $\Lambda = \Lambda_. = \Lambda_.$"; we read it as $\Lambda = \Lambda_m = \Lambda_{m+1}$,
  the lattice reached in (iii).)
(v) ("consider the case $p = 2$") is open-ended and not formalized.

**Proof sketch of (iv).** With $\Lambda = \Lambda_m = \Lambda_{m+1}$ we have $\Delta = p\Lambda$. Take an orthogonal
basis (O'Meara §92, $p \ne 2$), $c_j = \varphi(\vec b_j)$. If $|c_j| \le p^{-2}$, then $\vec b_j \in \Delta$
($\varphi(\vec x + \vec b_j) - \varphi(\vec x) = 2\varphi(\vec x, \vec b_j) + c_j \in c_j\mathbb Z_p$), so
$p^{-1}\vec b_j \in \Lambda$, impossible for a basis vector.
-/
import QuadFormsKB.Literature.Cassels.Ch8.LatticeBridge
import QuadFormsKB.Literature.OMeara.Sec82Max
import QuadFormsKB.Literature.OMeara.Sec92

namespace QuadFormsKB.Cassels

open Submodule OMeara

variable {p : ℕ} [hp : Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]

section Helpers

private theorem nadd (a b : ℚ_[p]) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max a b

private theorem nsub (a b : ℚ_[p]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)

private theorem norm_alg_le (r : ℤ_[p]) : ‖algebraMap ℤ_[p] ℚ_[p] r‖ ≤ 1 := PadicInt.norm_le_one r

private theorem pinv_le_one : (p : ℝ)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le)

private theorem pinv_pos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hp.out.pos)

private theorem norm_p_q : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p

private theorem algebraMap_p : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) = (p : ℚ_[p]) := by simp

/-- `Q (c + r d) - Q c = ρ (Q (c + d) - Q c - Q d) + ρ² Q d`, with `ρ` the image of `r`. -/
private theorem diff_eq (Q : QuadraticForm ℚ_[p] V) (c d : V) (r : ℤ_[p]) :
    Q (c + r • d) - Q c = algebraMap ℤ_[p] ℚ_[p] r * (Q (c + d) - Q c - Q d)
      + algebraMap ℤ_[p] ℚ_[p] r ^ 2 * Q d := by
  have h1 := OMeara.Q_add Q c (r • d)
  have h2 := OMeara.Q_add Q c d
  rw [OMeara.bil_rsmul_right, OMeara.Q_rsmul] at h1
  linear_combination h1 - algebraMap ℤ_[p] ℚ_[p] r * h2

omit [IsScalarTower ℤ_[p] ℚ_[p] V] in
/-- Integrality of `2 B(c, d)` from integrality of `Q` on a submodule. -/
private theorem int_two_bil {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1)
    {c d : V} (hc : c ∈ Λ) (hd : d ∈ Λ) : ‖Q (c + d) - Q c - Q d‖ ≤ 1 := by
  refine (nsub _ _).trans (max_le ((nsub _ _).trans (max_le (hint _ (Λ.add_mem hc hd)) (hint _ hc)))
    (hint _ hd))

private theorem mem_one_of_norm_le {x : ℚ_[p]} (h : ‖x‖ ≤ 1) : x ∈ (1 : Submodule ℤ_[p] ℚ_[p]) :=
  Submodule.mem_one.2 ⟨⟨x, h⟩, rfl⟩

private theorem norm_le_of_mem_one {x : ℚ_[p]} (h : x ∈ (1 : Submodule ℤ_[p] ℚ_[p])) : ‖x‖ ≤ 1 := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 h
  exact norm_alg_le y

end Helpers

/-- **Cassels' lattice $\Gamma$** (Cassels 1978, Ch. 8, Example 8 (i), p. 126): for a $\mathbb Z_p$-submodule
$\Lambda$ of $V$, the $\vec d \in \Lambda$ with $\varphi(\vec c + \vec d) \equiv \varphi(\vec c) \pmod p$, i.e.
$|\varphi(\vec c + \vec d) - \varphi(\vec c)| \le p^{-1}$, for all $\vec c \in \Lambda$. -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (i), p. 126 (the lattice Γ)"]
def ex8Op (Q : QuadraticForm ℚ_[p] V) (Λ : Submodule ℤ_[p] V) : Submodule ℤ_[p] V where
  carrier := {d | d ∈ Λ ∧ ∀ c ∈ Λ, ‖Q (c + d) - Q c‖ ≤ (p : ℝ)⁻¹}
  add_mem' := by
    rintro d d' ⟨hd, h⟩ ⟨hd', h'⟩
    refine ⟨Λ.add_mem hd hd', fun c hc => ?_⟩
    have e : Q (c + (d + d')) - Q c = (Q ((c + d) + d') - Q (c + d)) + (Q (c + d) - Q c) := by
      rw [← add_assoc]; ring
    rw [e]
    exact (nadd _ _).trans (max_le (h' _ (Λ.add_mem hc hd)) (h c hc))
  zero_mem' := by
    refine ⟨Λ.zero_mem, fun c _ => ?_⟩
    simp [pinv_pos.le]
  smul_mem' := by
    rintro r d ⟨hd, h⟩
    refine ⟨Λ.smul_mem r hd, fun c hc => ?_⟩
    have hQd : ‖Q d‖ ≤ (p : ℝ)⁻¹ := by simpa using h 0 Λ.zero_mem
    have h1 : ‖Q (c + d) - Q c - Q d‖ ≤ (p : ℝ)⁻¹ := (nsub _ _).trans (max_le (h c hc) hQd)
    have hr := norm_alg_le r
    show ‖Q (c + r • d) - Q c‖ ≤ (p : ℝ)⁻¹
    rw [diff_eq]
    refine (nadd _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc _ ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul hr h1 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [norm_mul, norm_pow]
      calc _ ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul (pow_le_one₀ (norm_nonneg _) hr) hQd (norm_nonneg _) zero_le_one
        _ = _ := one_mul _

private theorem smul_mem_ex8Op {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V}
    (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1) {x : V} (hx : x ∈ Λ) : (p : ℤ_[p]) • x ∈ ex8Op Q Λ := by
  refine ⟨Λ.smul_mem _ hx, fun c hc => ?_⟩
  rw [diff_eq, algebraMap_p]
  have h1 := int_two_bil hint hc hx
  have h2 := hint x hx
  have h3 := pinv_le_one (p := p)
  have h4 := pinv_pos (p := p)
  refine (nadd _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, norm_p_q]
    nlinarith [norm_nonneg (Q (c + x) - Q c - Q x)]
  · rw [norm_mul, norm_pow, norm_p_q]
    nlinarith [norm_nonneg (Q x)]

private theorem mem_ex8Op {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} {d : V} :
    d ∈ ex8Op Q Λ ↔ d ∈ Λ ∧ ∀ c ∈ Λ, ‖Q (c + d) - Q c‖ ≤ (p : ℝ)⁻¹ := Iff.rfl

/-- **Cassels' sequence $\Lambda_m$** (Cassels 1978, Ch. 8, Example 8 (ii)–(iii), p. 126): $\Lambda_0 = \Lambda$ and
$\Lambda_{m+1} = p^{-1}\Delta_m$, where $\Gamma_m$ = `ex8Op Q Λ_m` and $\Delta_m$ is obtained from $\Gamma_m$ as
$\Gamma_m$ was from $\Lambda_m$ but with $p^{-1}\varphi$ instead of $\varphi$ (the $\vec e \in \Gamma_m$ with
$\varphi(\vec d + \vec e) \equiv \varphi(\vec d) \pmod{p^{2}}$ for all $\vec d \in \Gamma_m$). Here
$p^{-1}\Delta = \{\vec x \in V : p\vec x \in \Delta\}$ (`comap` of multiplication by $p$). -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (ii)–(iii), p. 126 (the lattices Δ and Λ_m)"]
noncomputable def ex8Seq (Q : QuadraticForm ℚ_[p] V) (Λ : Submodule ℤ_[p] V) : ℕ → Submodule ℤ_[p] V
  | 0 => Λ
  | m + 1 => (ex8Op ((p : ℚ_[p])⁻¹ • Q) (ex8Op Q (ex8Seq Q Λ m))).comap ((p : ℤ_[p]) • LinearMap.id)

private theorem mem_seq_succ {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} {m : ℕ} {x : V} :
    x ∈ ex8Seq Q Λ (m + 1) ↔ (p : ℤ_[p]) • x ∈ ex8Op ((p : ℚ_[p])⁻¹ • Q) (ex8Op Q (ex8Seq Q Λ m)) := Iff.rfl

private theorem seq_integral {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1)
    (m : ℕ) : ∀ c ∈ ex8Seq Q Λ m, ‖Q c‖ ≤ 1 := by
  induction m with
  | zero => exact hint
  | succ m _ =>
    intro x hx
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h := (mem_ex8Op.1 (mem_seq_succ.1 hx)).2 0 (zero_mem _)
    simp only [QuadraticMap.smul_apply, zero_add, QuadraticMap.map_zero, mul_zero, sub_zero, smul_eq_mul,
      OMeara.Q_rsmul, algebraMap_p] at h
    rw [show (p : ℚ_[p])⁻¹ * ((p : ℚ_[p]) ^ 2 * Q x) = (p : ℚ_[p]) * Q x by field_simp, norm_mul, norm_p_q] at h
    exact le_of_mul_le_mul_left (by simpa using h) pinv_pos

/-- **Cassels, Ch. 8, Example 8 (i)(a)** (p. 126): *let $\Lambda$ be a $\mathbb Z_p$-lattice in $V$ with
$\varphi(\vec c) \in \mathbb Z_p$ for all $\vec c \in \Lambda$; then $\Gamma$ is a lattice.* -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (i)(a), p. 126"]
theorem ex8_isLattice {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} (hΛ : Λ.IsLattice ℚ_[p])
    (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1) : (ex8Op Q Λ).IsLattice ℚ_[p] := by
  have hfg : (ex8Op Q Λ).FG := Submodule.FG.of_le hΛ.fg (fun d hd => hd.1)
  refine ⟨hfg, ?_⟩
  rw [eq_top_iff, ← hΛ.span_eq_top, Submodule.span_le]
  intro l hl
  have hpl : (p : ℤ_[p]) • l ∈ ex8Op Q Λ := smul_mem_ex8Op hint hl
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [SetLike.mem_coe, show l = (p : ℚ_[p])⁻¹ • ((p : ℤ_[p]) • l) by
    rw [← algebraMap_smul ℚ_[p] (p : ℤ_[p]) l, algebraMap_p, smul_smul, inv_mul_cancel₀ hp0, one_smul]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hpl)

/-- **Cassels, Ch. 8, Example 8 (i)(b)** (p. 126): $\varphi(\vec d) \in p\mathbb Z_p$ for all $\vec d \in \Gamma$. -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (i)(b), p. 126"]
theorem ex8_norm (Q : QuadraticForm ℚ_[p] V) (Λ : Submodule ℤ_[p] V) :
    ∀ d ∈ ex8Op Q Λ, ‖Q d‖ ≤ (p : ℝ)⁻¹ := fun d hd => by simpa using hd.2 0 Λ.zero_mem

/-- **Cassels, Ch. 8, Example 8 (i)(c)** (p. 126): *if $\varphi(\vec c) \in \mathbb Z_p$ for all
$\vec c \in \Lambda$, then $p\Lambda \subseteq \Gamma \subseteq \Lambda$.* Here $p\Lambda$ is the image of $\Lambda$
under multiplication by $p$. -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (i)(c), p. 126"]
theorem ex8_between {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1) :
    Λ.map ((p : ℤ_[p]) • LinearMap.id) ≤ ex8Op Q Λ ∧ ex8Op Q Λ ≤ Λ := by
  refine ⟨?_, fun d hd => hd.1⟩
  rintro _ ⟨x, hx, rfl⟩
  simpa using smul_mem_ex8Op hint hx

/-- **Cassels, Ch. 8, Example 8 (ii)** (p. 126): *let $\Delta$ be obtained from $\Gamma$ as $\Gamma$ was from
$\Lambda$ but with $p^{-1}\varphi$ instead of $\varphi$; then $\Delta \supseteq p\Lambda$* (inclusion reconstructed:
the scan is garbled). -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (ii), p. 126 (inclusion reconstructed)"]
theorem ex8_ii {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1) :
    Λ.map ((p : ℤ_[p]) • LinearMap.id) ≤ ex8Op ((p : ℚ_[p])⁻¹ • Q) (ex8Op Q Λ) := by
  rintro _ ⟨x, hx, rfl⟩
  have hy : (p : ℤ_[p]) • x ∈ ex8Op Q Λ := smul_mem_ex8Op hint hx
  refine ⟨by simpa using hy, fun d hd => ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h := diff_eq Q d x (p : ℤ_[p])
  rw [algebraMap_p] at h
  have e : ((p : ℚ_[p])⁻¹ • Q) (d + (p : ℤ_[p]) • x) - ((p : ℚ_[p])⁻¹ • Q) d
      = (Q (d + x) - Q d - Q x) + (p : ℚ_[p]) * Q x := by
    simp only [QuadraticMap.smul_apply, smul_eq_mul]
    calc (p : ℚ_[p])⁻¹ * Q (d + (p : ℤ_[p]) • x) - (p : ℚ_[p])⁻¹ * Q d
        = (p : ℚ_[p])⁻¹ * (Q (d + (p : ℤ_[p]) • x) - Q d) := by ring
      _ = (p : ℚ_[p])⁻¹ * ((p : ℚ_[p]) * (Q (d + x) - Q d - Q x) + (p : ℚ_[p]) ^ 2 * Q x) := by rw [h]
      _ = _ := by field_simp
  have hdx := hd.2 x hx
  have hQd := ex8_norm Q Λ d hd
  rw [e]
  refine (nadd _ _).trans (max_le ?_ ?_)
  · have : Q (d + x) - Q d - Q x = (Q (x + d) - Q x) - Q d := by rw [add_comm d x]; ring
    rw [this]
    exact (nsub _ _).trans (max_le hdx hQd)
  · rw [norm_mul, norm_p_q]
    nlinarith [norm_nonneg (Q x), hint x hx, pinv_pos (p := p)]

/-- **Cassels, Ch. 8, Example 8 (iii)** (p. 126), first part: $\Lambda_m \subseteq \Lambda_{m+1}$ for all $m$. -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (iii), p. 126 (Λ_m ⊆ Λ_{m+1})"]
theorem ex8_seq_mono {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1) (m : ℕ) :
    ex8Seq Q Λ m ≤ ex8Seq Q Λ (m + 1) := by
  intro x hx
  exact mem_seq_succ.2 (ex8_ii (seq_integral hint m) ⟨x, hx, by simp⟩)

/-- **Cassels, Ch. 8, Example 8 (iii)** (p. 126): $\varphi$ is integer-valued on each $\Lambda_m$. -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (iii), p. 126 (φ integer-valued on Λ_m)"]
theorem ex8_seq_integral {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1)
    (m : ℕ) : ∀ c ∈ ex8Seq Q Λ m, ‖Q c‖ ≤ 1 := by
  exact seq_integral hint m

private theorem le_seq {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1) (m : ℕ) :
    Λ ≤ ex8Seq Q Λ m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact ih.trans (ex8_seq_mono hint m)

private theorem one_fg : (1 : Submodule ℤ_[p] ℚ_[p]).FG := by
  rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _

private theorem seq_le_dual {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1)
    (m : ℕ) : ex8Seq Q Λ m ≤ OMeara.dualLatMax Q 1 Λ := by
  intro v hv k hk
  have h := int_two_bil (seq_integral hint m) hv (le_seq hint m hk)
  have e : 2 * OMeara.bil Q v k = Q (v + k) - Q v - Q k := by
    rw [OMeara.Q_add Q v k]; ring
  rw [e]
  exact mem_one_of_norm_le h

/-- **Cassels, Ch. 8, Example 8 (iii)** (p. 126): each $\Lambda_m$ is a lattice on $V$. -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (iii), p. 126 (Λ_m is a lattice)"]
theorem ex8_seq_isLattice [FiniteDimensional ℚ_[p] V] {Q : QuadraticForm ℚ_[p] V}
    (hV : (QuadraticMap.associated Q).Nondegenerate) {Λ : Submodule ℤ_[p] V} (hΛ : Λ.IsLattice ℚ_[p])
    (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1) (m : ℕ) : (ex8Seq Q Λ m).IsLattice ℚ_[p] := by
  have hfg : (ex8Seq Q Λ m).FG :=
    Submodule.FG.of_le (OMeara.fg_dualLatMax Q hV one_fg hΛ) (seq_le_dual hint m)
  exact Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ_[p] (le_seq hint m) hfg

/-- **Cassels, Ch. 8, Example 8 (iii)** (p. 126): *deduce that there is some $m$ such that
$\Lambda_{m+1} = \Lambda_m$* (for a regular space $V$, where the $\Lambda_m$ lie in a fixed lattice). -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (iii), p. 126 (the sequence becomes stationary)"]
theorem ex8_seq_stabilizes [FiniteDimensional ℚ_[p] V] {Q : QuadraticForm ℚ_[p] V}
    (hV : (QuadraticMap.associated Q).Nondegenerate) {Λ : Submodule ℤ_[p] V} (hΛ : Λ.IsLattice ℚ_[p])
    (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1) : ∃ m, ex8Seq Q Λ (m + 1) = ex8Seq Q Λ m := by
  set K' := OMeara.dualLatMax Q 1 Λ with hK'
  have hfg : K'.FG := OMeara.fg_dualLatMax Q hV one_fg hΛ
  have : Module.Finite ℤ_[p] K' := Module.Finite.iff_fg.mpr hfg
  have hN : IsNoetherian ℤ_[p] K' := inferInstance
  let f : ℕ →o Submodule ℤ_[p] K' :=
    ⟨fun m => (ex8Seq Q Λ m).comap K'.subtype, fun a b hab => Submodule.comap_mono (by
      induction hab with
      | refl => exact le_rfl
      | step _ ih => exact ih.trans (ex8_seq_mono hint _))⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.mpr hN) f
  have e : ∀ m, (f m).map K'.subtype = ex8Seq Q Λ m := fun m => by
    show ((ex8Seq Q Λ m).comap K'.subtype).map K'.subtype = _
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr (seq_le_dual hint m)
  refine ⟨n, ?_⟩
  rw [← e (n + 1), ← e n, hn (n + 1) (Nat.le_succ n)]

/-- **Cassels, Ch. 8, Example 8 (iv)** (p. 126): *suppose that $p \ne 2$ and that $\Lambda = \Lambda_m = \Lambda_{m+1}$.
Then $\Lambda$ has a basis $\vec b_1, \dots, \vec b_n$ such that $\varphi(\sum x_j\vec b_j) = \sum c_jx_j^{2}$ where
$|c_j| = 1$ or $p^{-1}$ for each $j$.* The basis is indexed by $0, \dots, n-1$; "$\varphi(\sum x_j\vec b_j) =
\sum c_jx_j^{2}$" is orthogonality, with $c_j = \varphi(\vec b_j)$. -/
@[kb "cassels1978" "Ch. 8, Ex. 8 (iv), p. 126"]
theorem ex8_iv [FiniteDimensional ℚ_[p] V] (hp2 : p ≠ 2) {Q : QuadraticForm ℚ_[p] V}
    (hV : (QuadraticMap.associated Q).Nondegenerate) {Λ : Submodule ℤ_[p] V} (hΛ : Λ.IsLattice ℚ_[p])
    (hint : ∀ c ∈ Λ, ‖Q c‖ ≤ 1) {m : ℕ} (hm : ex8Seq Q Λ (m + 1) = ex8Seq Q Λ m) :
    ∃ b : Module.Basis (Fin (Module.finrank ℤ_[p] (ex8Seq Q Λ m))) ℤ_[p] (ex8Seq Q Λ m),
      (∀ i j, i ≠ j → OMeara.bil Q (b i : V) (b j : V) = 0) ∧
      ∀ j, ‖Q (b j : V)‖ = 1 ∨ ‖Q (b j : V)‖ = (p : ℝ)⁻¹ := by
  set L := ex8Seq Q Λ m with hL
  have hLlat : L.IsLattice ℚ_[p] := ex8_seq_isLattice hV hΛ hint m
  have hLint := seq_integral hint m
  have h2 : IsUnit (2 : ℤ_[p]) := by
    have : IsUnit ((2 : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.2
      (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2))
    simpa using this
  have hreg : OMeara.IsRegular Q L := OMeara.isRegular_of_lattice_max Q hV hLlat
  obtain ⟨b, horth, hne⟩ := OMeara.exists_orthogonal_basis Q h2 hLlat.fg hreg
  refine ⟨b, horth, fun j => ?_⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hcoef : ∀ d : L, OMeara.bil Q (d : V) (b j : V) = algebraMap ℤ_[p] ℚ_[p] (b.repr d j) * Q (b j : V) := by
    intro d
    have hd : (d : V) = ∑ i, b.repr d i • (b i : V) := by
      have := congrArg (fun z : L => (z : V)) (b.sum_repr d)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hd, OMeara.bil_sum_left, Finset.sum_eq_single j]
    · rw [OMeara.bil_rsmul_left, OMeara.bil_self]
    · intro i _ hij
      rw [OMeara.bil_rsmul_left, horth i j hij, mul_zero]
    · simp
  have hdiff : ∀ d : L, ∃ s : ℤ_[p], Q ((d : V) + b j) - Q d = algebraMap ℤ_[p] ℚ_[p] s * Q (b j : V) := by
    intro d
    refine ⟨2 * b.repr d j + 1, ?_⟩
    have := OMeara.Q_add Q (d : V) (b j : V)
    rw [hcoef d] at this
    simp only [map_add, map_mul, map_one, map_ofNat]
    linear_combination this
  set c := Q (b j : V) with hc
  have hc0 : c ≠ 0 := hne j
  have hc1 : ‖c‖ ≤ 1 := hLint _ (b j).2
  rcases hc1.lt_or_eq with hlt | heq
  swap
  · exact Or.inl heq
  rcases (show ‖c‖ ≤ (p : ℝ) ^ (-1 : ℤ) from
    (Padic.norm_lt_pow_iff_norm_le_pow_sub_one c 0).1 (by simpa using hlt) |> fun h => by simpa using h).lt_or_eq
    with hlt2 | heq2
  swap
  · right; simpa using heq2
  exfalso
  have hc2 : ‖c‖ ≤ ((p : ℝ)⁻¹) ^ 2 := by
    have := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one c (-1)).1 hlt2
    rw [show ((-1 : ℤ) - 1) = -(2 : ℕ) by norm_num, zpow_neg, zpow_natCast] at this
    rw [inv_pow]; exact this
  -- `b j` lies in `Δ`
  have hbΓ : (b j : V) ∈ ex8Op Q L := by
    refine ⟨(b j).2, fun x hx => ?_⟩
    obtain ⟨s, hs⟩ := hdiff ⟨x, hx⟩
    simp only at hs
    rw [hs, norm_mul]
    calc _ ≤ 1 * ‖c‖ := mul_le_mul (norm_alg_le s) le_rfl (norm_nonneg _) zero_le_one
      _ ≤ ((p : ℝ)⁻¹) ^ 2 := by rw [one_mul]; exact hc2
      _ ≤ (p : ℝ)⁻¹ := by nlinarith [pinv_pos (p := p), pinv_le_one (p := p)]
  have hbΔ : (b j : V) ∈ ex8Op ((p : ℚ_[p])⁻¹ • Q) (ex8Op Q L) := by
    refine ⟨hbΓ, fun d hd => ?_⟩
    obtain ⟨s, hs⟩ := hdiff ⟨d, hd.1⟩
    simp only at hs
    simp only [QuadraticMap.smul_apply, smul_eq_mul]
    rw [← mul_sub, hs, norm_mul, norm_mul, norm_inv, norm_p_q, inv_inv]
    calc (p : ℝ) * (‖algebraMap ℤ_[p] ℚ_[p] s‖ * ‖c‖) ≤ (p : ℝ) * (1 * ((p : ℝ)⁻¹) ^ 2) := by
          gcongr
          exact norm_alg_le s
      _ = (p : ℝ)⁻¹ := by field_simp
  set y : V := (p : ℚ_[p])⁻¹ • (b j : V) with hy
  have hpy : (p : ℤ_[p]) • y = (b j : V) := by
    rw [← algebraMap_smul ℚ_[p] (p : ℤ_[p]) y, algebraMap_p, hy, smul_smul, mul_inv_cancel₀ hp0, one_smul]
  have hyL : y ∈ L := by
    have : y ∈ ex8Seq Q Λ (m + 1) := mem_seq_succ.2 (by rw [hpy]; exact hbΔ)
    rwa [hm] at this
  have heq1 : (p : ℤ_[p]) • (⟨y, hyL⟩ : L) = b j := Subtype.ext hpy
  have h1 := congrArg (fun z : L => b.repr z j) heq1
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self, Finsupp.single_eq_same] at h1
  have h3 := congrArg norm h1
  rw [norm_mul, PadicInt.norm_p, norm_one] at h3
  have h4 := PadicInt.norm_le_one (b.repr ⟨y, hyL⟩ j)
  have h5 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  nlinarith [norm_nonneg (b.repr ⟨y, hyL⟩ j), pinv_pos (p := p)]

end QuadFormsKB.Cassels
