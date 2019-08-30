method breakParagraphs(n: nat, b: bool, r: nat)
  requires r > 0
{
   var R1 := 0;
   var R2 := 0;
   var i := 0;
   var m := 0;
   while i < n
      invariant m <= n; // Global invariant
      invariant R1+m <= i; // Local invariant
   {
      i := i + r;
      if (i < n) {
          if (b) {
            m := m + r;
          } else {
            R1 := R1 + m;
            assert R1 <= n; // Bound
            m := 0;
          }
      }
   }
   assert 0<= m <= n; // Global invariant
   R2 := R2 + m;
   assert R2 <= n; // Bound
}