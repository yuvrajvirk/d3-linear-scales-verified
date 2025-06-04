module Interpolate {
    // export default function(a, b) {
    //   return a = +a, b = +b, function(t) {
    //     return a * (1 - t) + b * t;
    //   };
    // }

    function linearInterpolate(a: real, b: real): (real) -> real
    {
        (t: real)  => a * (1.0 - t) + b * t
    }

    lemma linearInterpolateEndpoints(a: real, b: real)
        ensures linearInterpolate(a, b)(0.0) == a && 
                linearInterpolate(a, b)(1.0) == b
    {
    }

    lemma mulNonNeg(x: real, y: real)
        requires x >= 0.0
        requires y >= 0.0
        ensures x * y >= 0.0
    {
    }

    lemma linearInterpolateLowerBound(a: real, b: real)
        requires a <= b
        ensures forall t :: 0.0 <= t <= 1.0 ==> 
            linearInterpolate(a, b)(t) >= a
    {
        forall t | 0.0 <= t <= 1.0
        ensures linearInterpolate(a, b)(t) >= a
        {
            mulNonNeg(b - a, t);
            assert a + (b - a) * t >= a;
        }
    }

    lemma linearInterpolateUpperBound(a: real, b: real)
        requires a <= b
        ensures forall t :: 0.0 <= t <= 1.0 ==> 
            linearInterpolate(a, b)(t) <= b
    {
    }

    lemma linearInterpolateMonotonic(a: real, b: real)
        ensures forall t1, t2 :: 0.0 <= t1 <= t2 <= 1.0 && a >= b ==> 
            linearInterpolate(a, b)(t1) >= linearInterpolate(a, b)(t2)
        ensures forall t1, t2 :: 0.0 <= t1 <= t2 <= 1.0 && a <= b ==> 
            linearInterpolate(a, b)(t1) <= linearInterpolate(a, b)(t2)
    {
    }

    lemma linearInterpolateConstantRate(a: real, b: real)
        ensures forall t1, t2 :: 0.0 <= t1 <= 1.0 && 0.0 <= t2 <= 1.0 && t1 != t2 ==>
            (linearInterpolate(a, b)(t1) - linearInterpolate(a, b)(t2)) / (t1 - t2) == b - a
    {
    }

    // method testLinearInterpolate()
    // {
    //     var interpolator := linearInterpolate(0.0, 1.0);
    //     assert interpolator(0.0) == 0.0;  // At t=0, should return a
    //     assert interpolator(1.0) == 1.0;  // At t=1, should return b
    //     assert interpolator(0.5) == 0.5;  // At t=0.5, should return midpoint
    // }
}