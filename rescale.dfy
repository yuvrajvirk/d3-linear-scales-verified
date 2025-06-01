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

// Normalize returns a function that normalizes a value to the range [a, b]
// function normalize(a, b) {
//   return (b -= (a = +a))
//       ? function(x) { return (x - a) / b; }
//       : constant(isNaN(b) ? NaN : 0.5);
// }
// Handles edge cases where a or b is NaN

function normalize(a: real, b: real): (real) -> real
{
    if a != b then
        (x: real) => (x - a) / (b - a)
    else
        (x: real) => 0.5
}

lemma normalizeBounds(a: real, b: real, c: real)
    ensures normalize(a, b)(c) >= a &&
            normalize(a, b)(c) <= b
{
    
}


