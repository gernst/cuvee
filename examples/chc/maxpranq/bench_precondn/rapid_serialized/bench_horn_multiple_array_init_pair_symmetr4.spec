func main()
{
        Int[] a;
	Int[] b;
	Int[] c;
        const Int alength;
        Int i = 1;

        while(i < alength)
        {
	    const Int x;
            const Int y;
	  if (y >= x) {
	    a[i] = x;
	    b[i] = y;
	    i = i + 1;
	  } else {
	    skip;
	  }
	}
        i = 0;
        while (i < alength)
        {
          c[i] = b[i] - a[i];
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
       (>= (c main_end pos) 0)
      )
   )
)
