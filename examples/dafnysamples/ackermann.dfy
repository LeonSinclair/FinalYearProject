//source: https://rise4fun.com/Dafny/Ackermann visited 7/4/19
function Ackermann(m: int, n: int): int
  // The following lexicographic pair allows Dafny to prove termination.
  // Still, you may not want to sit around and wait for a call to Ackermann
  // to terminate.
  decreases m, n
{
  if m <= 0 then
    n + 1
  else if n <= 0 then
    Ackermann(m - 1, 1)
  else
    Ackermann(m - 1, Ackermann(m, n - 1))
}