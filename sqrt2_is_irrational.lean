import Mathlib

set_option linter.style.emptyLine false

-- a と b が互いに素な正の整数であるとする。
-- a² = 2b² ならば矛盾することを証明する。
theorem sqrt_two_contradiction
    (a b : ℕ)
    (hcop : Nat.Coprime a b)
    (h : a ^ 2 = 2 * b ^ 2) :
    False := by
  -- 2 は素数である。
  have hp : Nat.Prime 2 := by norm_num

  -- a² = 2b² より、2 は a² を割り切る。
  have ha_sq : 2 ∣ a ^ 2 := by
    rw [h]
    exact dvd_mul_right 2 (b ^ 2)

  -- 2 が a² を割り切るので、2 は a を割り切る。
  have ha_even : 2 ∣ a :=
    hp.dvd_of_dvd_pow ha_sq

  -- a = 2k と表す。
  rcases ha_even with ⟨k, hk⟩

  -- a² = 2b² に a = 2k を代入すると b² = 2k²。
  have hb_sq : b ^ 2 = 2 * k ^ 2 := by
    nlinarith [h, hk]

  -- 同様に、2 は b² を割り切る。
  have hb_sq_dvd : 2 ∣ b ^ 2 := by
    rw [hb_sq]
    exact dvd_mul_right 2 (k ^ 2)

  -- 素数の性質から 2 は b も割り切る。
  have hb_even : 2 ∣ b :=
    hp.dvd_of_dvd_pow hb_sq_dvd

  -- 2 が a と b の両方を割り切るので、
  -- 2 は gcd(a,b) も割り切る。
  have hgcd : 2 ∣ Nat.gcd a b := by
    apply Nat.dvd_gcd
    · omega
    · exact hb_even

  -- 互いに素なので gcd(a,b) = 1。
  have hcop' : Nat.gcd a b = 1 := hcop

  -- 2 が 1 を割り切ることになり矛盾する。
  omega
