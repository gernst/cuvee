func main()
{
        Int[] a;
        Int[] b;
        Int[] c;
        const Int alength;
        Int i = 0;

        while(i < alength)
                         {
	                     const Int j;
                             const Int k;
            if (3 <= j+k) {
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
          c[i] = a[i] + b[i];
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
       (<= 3 (c main_end pos))
      )
   )
 )
