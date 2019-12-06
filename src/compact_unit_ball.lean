import analysis.normed_space.banach
import analysis.normed_space.basic
import linear_algebra.basic
import linear_algebra.basis
import linear_algebra.dimension
import linear_algebra.finite_dimensional
import topology.subset_properties
import set_theory.cardinal
import data.real.basic
import topology.sequences
import order.bounded_lattice
import analysis.specific_limits
import analysis.normed_space.finite_dimension

noncomputable theory
open_locale classical

local attribute [instance, priority 0] algebra.to_has_scalar
local attribute [instance, priority 200] vector_space.to_module

set_option class.instance_max_depth 100

open metric set

universe u

-- completeness of k is only assumed so we can use the library to prove that
-- the span of a finite set is closed. Can someone find a non-complete
-- field k and a normed vector space V over k in which there is finite
-- dimensional subspace which is not closed?
variables 
  {k : Type} [nondiscrete_normed_field k] [complete_space k] 
  {V : Type} [normed_group V] [normed_space k V]

lemma nontrivial_norm_gt_one: ∃ x : k, x ≠ 0 ∧ norm x > 1 :=
begin
  cases normed_field.exists_one_lt_norm k with x hx,
  existsi x,
  split,
  {
    intro hzero,
    rw hzero at hx,
    norm_num at hx,
  },{
    exact hx,
  },
end

lemma nontrivial_arbitrarily_small_norm 
  {e : ℝ} (he : e > 0) : ∃ x : k, x ≠ 0 ∧ norm x < e :=
begin
  cases normed_field.exists_norm_lt k he with x hx,
  existsi x,
  split, 
  {
    intro xzero,
    have h := hx.1,
    rw xzero at h,
    norm_num at h,
  },{
    exact hx.2,
  },
end

lemma nontrivial_norm_lt_one: 
  ∃ x : k, x ≠ 0 ∧ norm x < 1 :=
begin
  have one_gt_zero : (1 : ℝ) > 0,
    norm_num,
  exact nontrivial_arbitrarily_small_norm one_gt_zero, 
end

lemma ball_span_ash {A : set V}
  (hyp : ∀ v : V, norm v ≤ 1 → v ∈ submodule.span k A) (v : V) :
  v ∈ submodule.span k A :=
begin
  cases (classical.em (v = 0)) with v0 vn0,
  { rw submodule.mem_span,
    intros p hp,
    rw v0,
    exact submodule.zero_mem p,
  },
  have hw2 : norm v ≠ 0 := mt (norm_eq_zero v).1 vn0,
  have h1 : 1 / norm v > 0,
    norm_num,
    have h2 : 0 ≤ norm v := norm_nonneg v,
    rw le_iff_lt_or_eq at h2,
    cases h2 with h21 h22,
      exact h21,
      exfalso,
      have : norm v = 0,
      symmetry,
      exact h22,
      exact hw2 this,
  
  have h_small : ∃ x : k, x ≠ 0 ∧ norm x < 1 / norm v,
  exact nontrivial_arbitrarily_small_norm h1,
  cases h_small with x hx,
    set w : V := x • v with hwdef, -- "set" = "let + have".
    have hw : norm w ≤ 1,
    {
      rw le_iff_lt_or_eq,
      left,
      rw hwdef,
      rw norm_smul,
      have h3 : norm v > 0, 
      have := norm_nonneg v,
      rw le_iff_eq_or_lt at this,
      cases this with hzero hpos,
      exfalso,
      have h6 : norm v = 0,
      symmetry,
      exact hzero,
      exact hw2 h6,
      exact hpos,
      have h4 := hx.2,
      rw <- mul_lt_mul_right h3 at h4,
      have h5 : 1/norm v * norm v = 1, exact one_div_mul_cancel hw2,
      rw h5 at h4,
      exact h4,
    },
  rw <- submodule.smul_mem_iff (submodule.span k A) hx.1,
  rw <- hwdef,
  exact hyp w hw,
end

-- if A spans the closed unit ball then it spans all of V
lemma ball_span {A : set V}: (∀ v : V, v ∈ (closed_ball 0 1 : set V) 
  → v ∈ submodule.span k A) → ∀ v : V, v ∈ submodule.span k A :=
begin
  intro H,
  have hyp : ∀ v : V, norm v ≤ 1 → v ∈ submodule.span k A,
  intros v hv,
  rw <- dist_zero_right at hv,
  exact H v hv,
  exact ball_span_ash hyp,
end

theorem finite_dimensional_span_of_finite {A : set V} (hA : finite A) :
  finite_dimensional k ↥(submodule.span k A) :=
begin
  apply is_noetherian_of_fg_of_noetherian,
  exact submodule.fg_def.2 ⟨A, hA, rfl⟩,
end

-- the span of a finite set is (sequentially) closed
lemma finite_span_seq_closed
  (A : set V) : finite A → is_seq_closed (↑(submodule.span k A) : set V) :=
begin
  intro h_fin,
  apply is_seq_closed_of_is_closed,
  haveI : finite_dimensional k ↥(submodule.span k A) := finite_dimensional_span_of_finite h_fin,
  exact submodule.closed_of_finite_dimensional _,
end

--turns cover into a choice function
lemma cover_to_func (A X : set V) {r : ℝ} (hX : X ⊆ (⋃a ∈ A, ball a r))
  (a : V) (ha : a ∈ A) :
  ∃(f : V → V), ∀x, f x ∈ A ∧ (x ∈ X → x ∈ ball (f x) r) :=
begin
  classical,
  have : ∀(x : V), ∃a, a ∈ A ∧ (x ∈ X → x ∈ ball a r) :=
  begin
    assume x,
    by_cases h : x ∈ X,
    { simpa [h] using hX h },
    { exact ⟨a, ha, by simp [h]⟩ }
  end,
  choose f hf using this,
  exact ⟨f, λx, hf x⟩
end

-- if the closed unit ball is compact, then there is 
-- a function which selects the center of a ball of radius 1/2 close to it
lemma compact_choice_func (hc : compact (closed_ball 0 1 : set V))
  {r : k} (hr : norm r > 0) :
  ∃ A : set V, A ⊆ (closed_ball 0 1 : set V) ∧ finite A ∧
  ∃ f : V → V, ∀ x : V, f x ∈ A ∧ (x ∈ (closed_ball 0 1 : set V) 
  → x ∈ ball (f x) (1/norm r)) :=
begin
  let B : set V := closed_ball 0 1,
  have cover : B ⊆ ⋃ a ∈ B, ball a (1 / norm r),
    {
        intros x hx,
        simp,
        use x,
        rw dist_self,
        split,
        simp at hx,
        exact hx,
        norm_num,
        exact hr,
    },
    obtain ⟨A, A_sub, A_fin, HcoverA⟩ :
    ∃ A ⊆ B, finite A ∧ B ⊆ ⋃ a ∈ A, ball a (1/ norm r) :=
        compact_elim_finite_subcover_image hc (by simp[is_open_ball]) cover,
    
    -- need that A is non-empty to construct a choice function!
    have x_in : (0 : V) ∈ B,
    simp,
    norm_num,

    obtain ⟨a, a_in, ha⟩ : ∃ a ∈ A, dist (0 : V) a < 1/ norm r,
      by simpa using HcoverA x_in,
    
    have hfunc := cover_to_func A B HcoverA a a_in,

    existsi A,
    split,
    exact A_sub,
    split,
    exact A_fin,
    exact hfunc,
end

def aux_seq (v : V) (x : k) (f : V → V) : ℕ → V
| 0 := v
| (n + 1) :=  x • (aux_seq n - f (aux_seq n))

def partial_sum (f : ℕ → V) : ℕ → V
| 0 := f 0
| (n + 1) := f (n + 1) + partial_sum n

def approx_seq (v : V) (x : k) (f : V → V) : ℕ → V :=
  partial_sum (λ n : ℕ, (1/x)^n • f(aux_seq v x f n))

-- if a sequence w n satisfies the bound |v - w n| < e^(n+1), where 0 < e < 1
-- then w n converges to v
lemma bound_power_convergence (w : ℕ → V) {v : V}
  {x : k} (hx : norm x > 1)
  (h : ∀ n : ℕ, norm (v - w n) ≤ (1 / norm x)^(n + 1)) :
  filter.tendsto w filter.at_top (nhds v) :=
begin
  have hlt1 : 1 / norm x < 1,
  {
    rw div_lt_one_iff_lt,
    exact hx,
    apply lt_trans zero_lt_one,
    exact hx,
  },
  have hpos : 1 / norm x > 0,
  {
    norm_num,
    apply lt_trans zero_lt_one,
    exact hx,
  },
  have H : ∀ n : ℕ, norm (w n - v) ≤ (1 / norm x)^n,
  intro n,
  rw <- dist_eq_norm,
  rw dist_comm,
  rw dist_eq_norm,
  apply le_trans,
  exact h n,
  rw pow_succ,
  have h1 : (1 / norm x) * (1 / norm x)^n ≤ 1 * (1 / norm x)^n,
  rw mul_le_mul_right,
  rw le_iff_eq_or_lt,
  right,
  exact hlt1,
  apply pow_pos,
  exact hpos,
  rw one_mul at h1,
  exact h1,

  rw tendsto_iff_norm_tendsto_zero,
  apply squeeze_zero,
  intro t,
  exact norm_nonneg (w t - v),
  exact H,
  apply tendsto_pow_at_top_nhds_0_of_lt_1,
  rw le_iff_eq_or_lt,
  right,
  exact hpos,
  exact hlt1, 
end

-- the approximation sequence (w n below) is contained in the span of A
-- this is true since by construction w n is a linear combination 
-- of the elements in A
lemma approx_in_span (A : set V) (v : V) (x : k) (f : V → V) 
  (hf : ∀ x : V, f x ∈ A): 
  ∀ n : ℕ, approx_seq v x f n ∈ submodule.span k A :=
begin
  let w := approx_seq v x f,
  have hw : w = approx_seq v x f,
  refl,
  intro n,
  rw submodule.mem_span,
  intros p hp,
  induction n with n hn,
  {
    have h1 : w 0 = (1/x)^0 • f(v), refl,
    simp at h1,
    rw <- hw,
    rw h1,
    have h2 : f v ∈ A := hf v,
    exact hp h2,
  },{
    have h1 : w (n+1) = (1/x)^(n+1) • f(aux_seq v x f (n+1)) + w(n), 
    refl,
    rw <- hw,
    rw h1,
    have h2 := hp (hf (aux_seq v x f (n+1))),
    have h3 := submodule.smul_mem p ((1/x)^(n+1)) h2,
    apply submodule.add_mem p,
    exact h3,
    exact hn,
  },
end

theorem compact_unit_ball_implies_finite_dim 
    (Hcomp : compact (closed_ball 0 1 : set V)) : finite_dimensional k V :=
begin
  -- there is an x in k such that norm x > 1
  have hbignum : ∃ x : k, x ≠ 0 ∧ norm x > 1,
  exact nontrivial_norm_gt_one,
  cases hbignum with x hx,

  have hxpos : norm x > 0,
  {
    have h : (1:ℝ) > 0,
    norm_num,
    exact gt_trans hx.2 h,
  },

  -- use compactness to find a finite set A
  -- and function f : V -> A such that for every 
  -- v in closed_ball 0 1, |f v - v| < 1/ norm x
  obtain ⟨A, A_sub, A_fin, Hexistsf⟩ := compact_choice_func Hcomp hxpos,
  obtain ⟨f, hf⟩ := Hexistsf,

  -- suffices to show closed_ball 0 1 is spanned by A
  apply finite_dimensional.of_fg,
  rw submodule.fg_def,
  existsi A,
  split,
  exact A_fin,
  rw submodule.eq_top_iff',
  apply ball_span,

  -- let v in closed_ball 0 1 and show that it is in the span of A
  -- to do so we construct a sequence w n such that
  -- w n -> v and w n in span A for all n 
  -- for this we do a kind of 'dyadic approximation' of v using the set A
  -- then we use that the span of a finite set is closed to conclude
  intros v hv,
  let u : ℕ → V := aux_seq v x f,
  let w : ℕ → V := partial_sum (λ n : ℕ, (1/x)^n • f(u(n))),

  -- show that w n is in the span of A
  have hw : ∀ n, w n ∈ submodule.span k A,
  {
    have hf' : ∀ x : V, f x ∈ A,
    intro x, 
    exact (hf x).1,
    exact approx_in_span A v x f hf',
  },

  -- this is just some algebraic manipulation
  have hdist : ∀ n : ℕ, v - w n = (1/x)^(n+1) • u (n+1),
  {
    intro n,
    induction n with n hn,
    {
      have h1 : w 0 = (1/x)^0 • f(v), refl,
      rw zero_add,
      rw pow_one,
      rw pow_zero at h1,
      rw one_smul at h1,
      rw h1,
      have h2 : u 1 = x • (v - f(v)), refl,
      rw h2,
      rw smul_smul,
      rw one_div_mul_cancel,
      rw one_smul,
      exact hx.1,
    }, {
      have h1 : w (n+1) = (1/x)^(n+1) • f(u (n+1)) + w(n), refl,
      have h2 : u (n+2) = x • (u (n+1) - f (u (n+1))), refl,
      rw h2,
      rw pow_succ,
      rw smul_smul,
      rw mul_comm,
      rw <- mul_assoc,
      rw mul_one_div_cancel,
      rw one_mul,
      rw smul_sub,
      rw <- hn,
      rw h1,
      rw add_comm _ (w n),
      rw sub_sub v (w n) _,
      exact hx.1,
    },
  },

  -- main bound for convergence using the expression hdist
  have hbound : ∀ n : ℕ, norm (v - w n) ≤ (1/norm x)^(n+1),
  {
    intro n,
    rw hdist n,
    rw norm_smul,
    have hu : u(n+1) = x • (u(n) - f(u(n))), refl,
    rw hu,
    have husmall : norm (u n) ≤ 1,
    {
      induction n with n hn,
      have h0 : u 0 = v, refl,
      rw h0,
      rw <- dist_zero_right,
      exact hv,

      have hu' : u(n + 1) = x • (u(n) - f(u(n))), refl,
      rw hu',
      have h2 := (hf (u n)).2,
      rw norm_smul,
      rw <- dist_eq_norm,
      have h3 := hn hu',
      rw <- dist_zero_right at h3,
      have h4 : dist (u n) (f (u n)) < 1/ norm x,
      exact h2 h3,
      rw le_iff_eq_or_lt,
      right,
      rw <- mul_lt_mul_left hxpos at h4,  
      rw mul_one_div_cancel at h4,
      exact h4,
      exact mt (norm_eq_zero x).1 hx.1,
    },
    have h2 : 0 < (1/norm x),
      norm_num,
      exact hxpos,
    have h1 : 0 < (1/ norm x)^(n+1),
      exact pow_pos h2 (n+1),
    have h3 : norm ((1/ x)^(n+1)) * norm (x • (u n - f(u n))) ≤ norm ((1/ x)^(n+1)) * 1 → 
      (1/norm x)^(n+1) * norm (x • (u n - f(u n))) ≤ (1/norm x)^(n+1),
    intro h,
    rw mul_one at h,
    rw normed_field.norm_pow at h,
    rw normed_field.norm_div at h,
    rw normed_field.norm_one at h,
    exact h,
    rw normed_field.norm_pow,
    rw normed_field.norm_div,
    rw normed_field.norm_one,
    apply h3,
    rw normed_field.norm_pow,
    rw normed_field.norm_div,
    rw normed_field.norm_one,
    rw mul_le_mul_left h1,
    rw norm_smul,
    rw <- dist_zero_right at husmall,
    have h4 := (hf (u n)).2 husmall,
    rw <- dist_eq_norm,
    rw <- mul_le_mul_left h2,
    rw <- mul_assoc,
    rw mul_one,
    rw one_div_mul_cancel,
    rw one_mul,
    rw le_iff_eq_or_lt,
    right,
    exact h4,
    exact mt (norm_eq_zero x).1 hx.1,
  },

  -- w n -> v as n -> infty
  have hlim : filter.tendsto w filter.at_top (nhds v : filter V)
    := bound_power_convergence w hx.2 hbound,
    
  -- the span of a finite set is (sequentially) closed
  let S : set V := ↑(submodule.span k A),
  have hspan_closed : is_seq_closed S := finite_span_seq_closed A A_fin,

  have hw' : ∀ n, w n ∈ S,
  exact hw,

  -- since S is closed, the limit v of w n is in S, as required.
  have hinS: v ∈ S,
  exact mem_of_is_seq_closed hspan_closed hw' hlim,
  exact hinS,
end
