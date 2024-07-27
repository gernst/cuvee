func main()
{
        Int[] a;
        Int[] b;
        const Int alength;
        Int i = 1;

        while(i < alength)
                     {
	                 const Int j;
                         const Int k;
            if (k <= j) {
                   a[i] = j;
                   b[i] = k;
                   i = i + 1;
               } else {
                   skip;
               }
        }
        i = 0;
        while (i < alength)
        {
          a[i] = a[i] + 1;
          b[i] = b[i] + 1;
          i = i + 1;
        }
}

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (< 0 pos)
          (< pos alength)
          (<= alength (i main_end))
         )
       (<= (b main_end pos) (a main_end pos))
      )
    )
 )
