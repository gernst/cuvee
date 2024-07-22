func main()
{
	Int[] a;
	Int[] b;
	const Int alength;

	Int i = 1;
	Int j;
	while(i < alength)
	     {
                 const Int k;
	  if (k >= j) {
	         a[i] = k;
                 i = i +1;
	  } else {
	    skip;
	  }
	}
	i = 0;
	while(i < alength)
	{
	  b[i] = a[i];
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
       (>= (b main_end pos) (j main_end))
      )
   )
)
