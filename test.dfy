module LinearInterpolation {

  function linearInterpolate(a: real, b: real): (real) -> real
    reads {}
  {
    (t: real) => a * (1.0 - t) + b * t
  }

  // Helper lemma: if x ≥ 0 and y ≥ 0 then x * y ≥ 0.
  lemma mulNonNeg(x: real, y: real)
    requires x >= 0.0
    requires y >= 0.0
    ensures  x * y >= 0.0
  {
  }

  lemma linearInterpolateBounded(a: real, b: real)
    requires a <= b
    ensures  forall t :: 0.0 <= t <= 1.0 ==> linearInterpolate(a, b)(t) >= a
  {
    forall t | 0.0 <= t <= 1.0
      ensures linearInterpolate(a, b)(t) >= a
    {
      // Invoke helper lemma to conclude (b - a) * t ≥ 0
      mulNonNeg(b - a, t);
      assert (b - a) * t >= 0.0;

      // Finally: a + ((b - a) * t) ≥ a + 0  ==  a
      calc {
        a + (b - a) * t;
        >= a + 0.0;   // since (b - a)*t ≥ 0.0
        == a;
      }
    }
  }
}
