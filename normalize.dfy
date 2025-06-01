// Normalize returns a function that normalizes a value to the range [a, b]
// function normalize(a, b) {
//   return (b -= (a = +a))
//       ? function(x) { return (x - a) / b; }
//       : constant(isNaN(b) ? NaN : 0.5);
// }
// Handles edge cases where a or b is NaN

function normalize(a: real, b: real): (real) -> real
{

}