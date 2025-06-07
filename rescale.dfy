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

lemma linearInterpolateLinear(a: real, b: real)
    ensures forall x :: 0.0 <= x <= 1.0 ==>
        linearInterpolate(a, b)(x) == a * (1.0 - x) + b * x
{
}

// Clamper returns a function that clamps a value to the range [a, b]
// function clamper(a, b) {
//   var t;
//   if (a > b) t = a, a = b, b = t;
//   return function(x) { return Math.max(a, Math.min(b, x)); };
// }

function min(a: real, b: real): real
{
    if a < b then a else b
}

function max(a: real, b: real): real
{
    if a > b then a else b
}

function clamper(a: real, b: real): (real) -> real
{
    if a > b then
        (x: real) => min(max(x, a), b)
    else
        (x: real) => min(max(x, b), a)
}

lemma clamperClamps(a: real, b: real, x: real) 
    ensures clamper(a, b)(x) >= min(a, b) &&
            clamper(a, b)(x) <= max(a, b)
{
}

// Determining intent: Based on use in interpolator, it should always produce values in [0, 1]
// function normalize(a, b) {
//   return (b -= (a = +a))
//       ? function(x) { return (x - a) / b; }
//       : constant(isNaN(b) ? NaN : 0.5);
// }
// Handles edge cases where a or b is NaN
// PROBLEMS:
// - assumes x is in [a, b]: Not explicit
// - assumes a <= b : Not explicit
// - if a == b, returns 0.5  : This is odd behavior

function normalize(a: real, b: real): (real) -> real
requires a <= b
{
    if a != b then
        (x: real) => (x - a) / (b - a)
    else
        (x: real) => 0.5
}

lemma divNonNeg(x: real, y: real)
    requires y > 0.0 && x >= 0.0
    ensures x / y >= 0.0
{
}

lemma normalizeLowerBound(a: real, b: real, c: real)
    requires a <= b && c >= a && c <= b
    ensures normalize(a, b)(c) >= 0.0 
{
    if a != b 
    {
        assert a < b;
        assert b - a > 0.0;
        assert c - a >= 0.0;
        divNonNeg(c - a, b - a);
    } 
    else 
    {
        assert normalize(a, b)(c) == 0.5;
    }
}

// Can't AND this with normalizeLowerBound despite same proof?
lemma normalizeUpperBound(a: real, b: real, c: real)
    requires a <= b && c >= a && c <= b
    ensures normalize(a, b)(c) <= 1.0
{
    if a != b 
    {
        assert a < b;
        assert b - a > 0.0;
        assert c - a >= 0.0;
        divNonNeg(c - a, b - a);
    } 
    else 
    { 
        assert normalize(a, b)(c) == 0.5;
    }
}

lemma divMonotonic(x1: real, x2: real, y: real)
    requires y > 0.0 && x1 <= x2
    ensures x1 / y <= x2 / y
{
}

lemma normalizeMonotonic(a: real, b: real)
    requires a <= b
    ensures forall x1, x2 :: a <= x1 <= x2 <= b ==> 
        normalize(a, b)(x1) <= normalize(a, b)(x2)
{
    forall x1, x2 | a <= x1 <= x2 <= b
    ensures normalize(a, b)(x1) <= normalize(a, b)(x2)
    {
        if a != b 
        {
            assert a < b;
            assert b - a > 0.0;
            assert x1 - a <= x2 - a;
            divMonotonic(x1 - a, x2 - a, b - a);
        } else {
            assert normalize(a, b)(x1) == 0.5;
            assert normalize(a, b)(x2) == 0.5;
        }
    }
}

lemma normalizeConstantRate(a: real, b: real)
    requires a < b
    ensures forall x1, x2 :: 0.0 <= x1 <= x2 <= 1.0 && x1 != x2 ==>
        (normalize(a, b)(x1) - normalize(a, b)(x2)) / (x1 - x2) == 1.0 / (b - a)
{
}

// Assume usage of bimap
// Bimap normalizes x to [0, 1] using domain [a, b] and then interpolates between range [c, d]
// function bimap(domain, range, interpolate) {
//   var d0 = domain[0], d1 = domain[1], r0 = range[0], r1 = range[1];
//   if (d1 < d0) d0 = normalize(d1, d0), r0 = interpolate(r1, r0);
//   else d0 = normalize(d0, d1), r0 = interpolate(r0, r1);
//   return function(x) { return r0(d0(x)); };
// }
// Points:
// - Normalize is an internal function used by bimap which checks implicit condition x <= y
// PROBLEMS:
// - may not be true that x is in [a, b]

function bimap(domain: seq<real>, range: seq<real>, interpolate: (real, real) -> real): (real) -> real
requires |domain| == 2 && |range| == 2
requires domain[0] <= domain[1]
requires range[0] <= range[1]
{
    var d0 := domain[0];
    var d1 := domain[1];
    var r0 := range[0];
    var r1 := range[1];
    var norm := normalize(d0, d1);
    var interp := linearInterpolate(r0, r1);
    (x: real) => interp(norm(x))
}

lemma bimapNormalizes(domain: seq<real>, range: seq<real>, interpolate: (real, real) -> real)
    requires |domain| == 2 && |range| == 2
    requires range[0] <= range[1]
    ensures forall x :: 0.0 <= x <= 1.0 && domain[0] <= x <= domain[1] ==> 
        bimap(domain, range, interpolate)(x) >= range[0] &&
        bimap(domain, range, interpolate)(x) <= range[1]
{
   forall x | 0.0 <= x <= 1.0 && domain[0] <= x <= domain[1]
   ensures bimap(domain, range, interpolate)(x) >= range[0] &&
           bimap(domain, range, interpolate)(x) <= range[1]
   {
       var norm := normalize(domain[0], domain[1]);
       var interp := linearInterpolate(range[0], range[1]);
       normalizeLowerBound(domain[0], domain[1], x);
       normalizeUpperBound(domain[0], domain[1], x);
       linearInterpolateLowerBound(range[0], range[1]);
       linearInterpolateUpperBound(range[0], range[1]);
       assert range[0] <= interp(norm(x)) <= range[1];
   }
}

lemma bimapMonotonic(domain: seq<real>, range: seq<real>, interpolate: (real, real) -> real)
    requires |domain| == 2 && |range| == 2
    requires range[0] <= range[1]
    ensures forall x1, x2 :: 0.0 <= x1 <= x2 <= 1.0 && domain[0] <= x1 <= domain[1] && domain[0] <= x2 <= domain[1] ==>
        bimap(domain, range, interpolate)(x1) <= bimap(domain, range, interpolate)(x2)
{
    forall x1, x2 | 0.0 <= x1 <= x2 <= 1.0 && domain[0] <= x1 <= domain[1] && domain[0] <= x2 <= domain[1]
    ensures bimap(domain, range, interpolate)(x1) <= bimap(domain, range, interpolate)(x2)
    {
        var norm := normalize(domain[0], domain[1]);
        var interp := linearInterpolate(range[0], range[1]);
        normalizeMonotonic(domain[0], domain[1]);
        linearInterpolateMonotonic(range[0], range[1]);
        assert interp(norm(x1)) <= interp(norm(x2));
    }
}

// Times out
// lemma bimapConstantRate(domain: seq<real>, range: seq<real>, interpolate: (real, real) -> real)
//     requires |domain| == 2 && |range| == 2
//     requires domain[0] <= domain[1]
//     requires range[0] <= range[1]
//     ensures forall x1, x2 :: 0.0 <= x1 <= x2 <= 1.0 && domain[0] <= x1 <= domain[1] && domain[0] <= x2 <= domain[1] && x1 != x2 ==>
//         (bimap(domain, range, interpolate)(x1) - bimap(domain, range, interpolate)(x2)) / (x1 - x2) == (range[1] - range[0]) / (domain[1] - domain[0])
// {
//     forall x1, x2 | 0.0 <= x1 <= x2 <= 1.0 && domain[0] <= x1 <= domain[1] && domain[0] <= x2 <= domain[1] && x1 != x2
//     ensures (bimap(domain, range, interpolate)(x1) - bimap(domain, range, interpolate)(x2)) / (x1 - x2) == (range[1] - range[0]) / (domain[1] - domain[0])
//     {
//         var norm := normalize(domain[0], domain[1]);
//         var interp := linearInterpolate(range[0], range[1]);
//         normalizeConstantRate(domain[0], domain[1]);
//         linearInterpolateConstantRate(range[0], range[1]);
//         assert (interp(norm(x1)) - interp(norm(x2))) / (x1 - x2) == (range[1] - range[0]) / (domain[1] - domain[0]);
//     }
// }   

// lemma bimapOutputsLinear(domain: seq<real>, range: seq<real>, interpolate: (real, real) -> real)
//     requires |domain| == 2 && |range| == 2
//     requires domain[0] < domain[1]
//     requires range[0] < range[1]
//     ensures forall x :: 0.0 <= x <= 1.0 && domain[0] <= x <= domain[1] ==>
//         bimap(domain, range, interpolate)(x) == x * (range[1] - range[0]) / (domain[1] - domain[0])
// {
//     forall x | 0.0 <= x <= 1.0 && domain[0] <= x <= domain[1]
//     ensures bimap(domain, range, interpolate)(x) == x * (range[1] - range[0]) / (domain[1] - domain[0])
//     {
//         var norm := normalize(domain[0], domain[1]);
//         var interp := linearInterpolate(range[0], range[1]);
//         normalizeConstantRate(domain[0], domain[1]);
//         linearInterpolateConstantRate(range[0], range[1]);
//         // assert (interp(norm(x)) - interp(norm(x))) / (x - x) == (range[1] - range[0]) / (domain[1] - domain[0]);
//     }
// }

lemma bimapLinearHelper(x: real, b: real, d: real)
    requires b > 0.0 && d > 0.0
{
    var t := x/b;
    assert linearInterpolate(0.0, d)(t) == 0.0 * (1.0 - t) + d * t;
    assert linearInterpolate(0.0, d)(t) == d * t;
    assert linearInterpolate(0.0, d)(t) == d * (x / b);
}

lemma bimapLinearFromZero(b: real, d: real)
    requires b > 0.0 && d > 0.0
    ensures forall x :: 0.0 <= x <= b ==>
        linearInterpolate(0.0, d)(normalize(0.0, b)(x)) == x * d / b
{
    forall x | 0.0 <= x <= b
    ensures linearInterpolate(0.0, d)(normalize(0.0, b)(x)) == x * d / b
    {
        var t := normalize(0.0, b)(x);
        assert t == x / b;  // This is the key missing step
        assert linearInterpolate(0.0, d)(t) == 0.0 * (1.0 - t) + d * t;
        assert linearInterpolate(0.0, d)(t) == d * t;
        assert linearInterpolate(0.0, d)(t) == d * (x / b);
        // Help Dafny with commutativity: d * (x / b) == (d * x) / b == x * d / b
        calc {
            linearInterpolate(0.0, d)(t);
        ==  d * (x / b);
        ==  d * x / b;
        ==  (d * x) / b;
        ==  (x * d) / b;
        ==  x * d / b;
        }
    }
}


class Transformer {
    const SENTINEL: real := -1000000000.0; 
    var domain: seq<real>;
    var range: seq<real>;
    var clamp: (real) -> real;
    // var piecewise: (seq<real>, seq<real>, (real, real) -> real) -> (real) -> real;
    var output: real;
    var input: real;
    var scale: (real) -> real;
    var interpolate: (real, real) -> real;
    var transform: (real) -> real;
    var untransform: (real) -> real;
    var invert: (real) -> real;

    constructor (t: (real) -> real, u: (real) -> real)
      ensures transform == t && untransform == u
      ensures |domain| == 2 && |range| == 2
    {
      transform   := t;
      untransform := u;
      domain   := [1.0, 1.0];
      range    := [1.0, 1.0];
      output := SENTINEL;
      input := SENTINEL;
    }

    // function rescale() {
    //     var n = Math.min(domain.length, range.length);
    //     if (clamp !== identity) clamp = clamper(domain[0], domain[n - 1]);
    //     piecewise = n > 2 ? polymap : bimap;
    //     output = input = null;
    //     return scale;
    //   }
    method rescale()
        requires |domain| == 2 && |range| == 2
        // requires domain[0] <= domain[1]
        // requires range[0] <= range[1]
        modifies this
    {
        this.clamp := clamper(domain[0], domain[1]);
        // this.piecewise := bimap;
        this.output := this.input;
    }

    // function scale(x) {
    //   return x == null || isNaN(x = +x) ? unknown : (output || (output = piecewise(domain.map(transform), range, interpolate)))(transform(clamp(x)));
    // }
    // This function scales an input value x using the configured transformation
    // Steps:
    // 1. First clamp x to the domain bounds using clamp function
    // 2. Apply the transform function to the clamped value
    // 3. If output function is not set:
    //    - Map the domain through transform function
    //    - Create piecewise function using transformed domain, range and interpolate
    //    - Store result in output
    // 4. Finally apply the output function to the transformed value

    method Scale(x: real) returns (r: real)
        requires |domain| == 2 && |range| == 2
        requires domain[0] < domain[1]
        requires range[0] < range[1]
        ensures this.output == this.input * (range[1] - range[0]) / (domain[1] - domain[0])
        modifies this
    {
      if output == SENTINEL {
        var tx := transform(clamp(x));
        // Need to prove that output is tx * (range[1] - range[0]) / (domain[1] - domain[0])
        this.output := bimap(domain, range, interpolate)(tx);
      }
      r := output;
    }

}

// export function identity(x) {
//   return x;
// }
function identity(x: real): real
{
    x
}

// export default function continuous() {
// return transformer()(identity, identity);
// }
method Continuous() returns (t: Transformer)
{
    // Pass identity for both transform & untransform:
    t := new Transformer(identity, identity);
    t.rescale();
}

function linearish(t: Transformer): Transformer
{
    // TODO: Implement linearish
    t 
}

method Linear(domain: seq<real>, range: seq<real>, scale: Transformer) returns (t: Transformer)
requires |domain| == 2
requires |range| == 2
requires domain[0] <= domain[1]
requires range[0] <= range[1]
ensures t == scale
ensures t.domain == domain
ensures t.range == range
ensures |t.domain| == 2
ensures |t.range| == 2
ensures t.domain[0] <= t.domain[1]
ensures t.range[0] <= t.range[1]
modifies scale
{
    scale.domain := domain;
    scale.range := range;
    return scale;
}

method testLinear(scale: Transformer)
modifies scale
{
    var linearScale := Linear([0.0, 100.0], [0.0, 500.0], scale);
    var result := linearScale.Scale(100.0);
    // assert scale output = input * (range[1] - range[0]) / (domain[1] - domain[0])
    assert result == 500.0;
}
